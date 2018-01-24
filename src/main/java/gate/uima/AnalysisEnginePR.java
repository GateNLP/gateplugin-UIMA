/*
 *  Copyright (c) 2005, The University of Sheffield.
 *
 *  This file is part of the GATE/UIMA integration layer, and is free
 *  software, released under the terms of the GNU Lesser General Public
 *  Licence, version 2.1 (or any later version).  A copy of this licence
 *  is provided in the file LICENCE in the distribution.
 *
 *  UIMA is a product of IBM, details are available from
 *  http://alphaworks.ibm.com/tech/uima
 */
package gate.uima;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URI;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

// UIMA imports
import org.apache.uima.UIMAFramework;
import org.apache.uima.analysis_engine.AnalysisEngine;
import org.apache.uima.analysis_engine.AnalysisEngineProcessException;
import org.apache.uima.cas.CAS;
import org.apache.uima.cas.CASRuntimeException;
import org.apache.uima.cas.ConstraintFactory;
import org.apache.uima.cas.FSIndex;
import org.apache.uima.cas.FSIndexRepository;
import org.apache.uima.cas.FSIterator;
import org.apache.uima.cas.FSMatchConstraint;
import org.apache.uima.cas.FSStringConstraint;
import org.apache.uima.cas.Feature;
import org.apache.uima.cas.FeaturePath;
import org.apache.uima.cas.FeatureStructure;
import org.apache.uima.cas.Type;
import org.apache.uima.cas.TypeSystem;
import org.apache.uima.cas.impl.XCASSerializer;
import org.apache.uima.cas.text.AnnotationFS;
import org.apache.uima.resource.ResourceInitializationException;
import org.apache.uima.resource.ResourceSpecifier;
import org.apache.uima.resource.metadata.ResourceMetaData;
import org.apache.uima.util.CasCreationUtils;
import org.apache.uima.util.InvalidXMLException;
import org.apache.uima.util.ProcessTrace;
import org.apache.uima.util.XMLInputSource;
import org.apache.uima.util.XMLParser;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import gate.Annotation;
import gate.AnnotationSet;
import gate.creole.AbstractLanguageAnalyser;
import gate.creole.ExecutionException;
import gate.creole.ResourceInstantiationException;
import gate.creole.metadata.CreoleParameter;
import gate.creole.metadata.CreoleResource;
import gate.creole.metadata.Optional;
import gate.creole.metadata.RunTime;
import gate.uima.mapping.GateAnnotationBuilder;
import gate.uima.mapping.MappingException;
import gate.uima.mapping.ObjectBuilder;
import gate.uima.mapping.ObjectManager;
import gate.uima.mapping.UIMAAnnotationBuilder;
import gate.uima.mapping.UIMAFeatureStructureBuilder;

/**
 * A processing resource that encapsulates a Text Analysis Engine from UIMA.
 */
@CreoleResource(name="UIMA Analysis Engine", comment="Wrapper for a Text Analysis Engine from UIMA.", helpURL="http://gate.ac.uk/userguide/chap:uima")
public class AnalysisEnginePR extends AbstractLanguageAnalyser {
  
  private static final long serialVersionUID = 6887409146460709861L;

  /** Version string for CVS. */
  @SuppressWarnings("unused")
  private static final String __CVSID = "$Id: AnalysisEnginePR.java 12299 2010-02-22 19:56:28Z ian_roberts $";

  private static final boolean DEBUG = false;

  ///// init parameters /////
  
  /**
   * URL to the UIMA XML descriptor for the contained analysis engine.
   */
  private URL analysisEngineDescriptor;

  /**
   * @return the location of the UIMA descriptor for the analysis engine.
   */
  public URL getAnalysisEngineDescriptor() {
    return analysisEngineDescriptor;
  }

  /**
   * Set the URL to the UIMA analysis engine descriptor.
   */
  @CreoleParameter(comment="The XML descriptor for the UIMA AE.  This must be a file: URL")
  public void setAnalysisEngineDescriptor(URL newDescriptor) {
    analysisEngineDescriptor = newDescriptor;
  }

  /**
   * URL to the XML file defining the mapping from GATE annotations to UIMA
   * feature structures, and the mapping from modifications to the UIMA feature
   * structures back into GATE.
   */
  private URL mappingDescriptor;

  /**
   * @return the location of the mapping descriptor.
   */
  public URL getMappingDescriptor() {
    return mappingDescriptor;
  }

  /**
   * Set the URL to the UIMA/GATE mapping descriptor.
   */
  @CreoleParameter(comment="The XML file describing the mapping between GATE and UIMA annotations")
  public void setMappingDescriptor(URL newDescriptor) {
    mappingDescriptor = newDescriptor;
  }

  ///// runtime parameters /////

  /**
   * The annotation set to use for annotations that are to be mapped to and
   * from UIMA.
   */
  private String annotationSetName = null;

  /**
   * Get the name of the annotation set to use for annotations that are to be
   * mapped to and from UIMA.
   */
  public String getAnnotationSetName() {
    return annotationSetName;
  }

  @RunTime
  @Optional
  @CreoleParameter(comment="The annotation set to use for annotations to be mapped to and from UIMA")
  public void setAnnotationSetName(String newName) {
    annotationSetName = newName;
  }
  
  ///// private variables /////

  /**
   * The UIMA analysis engine that actually does the work.
   */
  private AnalysisEngine analysisEngine;

  /**
   * The CAS used to pass annotations into and out of the TAE.
   */
  private CAS cas;

  /**
   * A List of ObjectBuilders defining the input mappings of GATE annotations
   * to UIMA annotations.
   */
  private List<UIMAFeatureStructureBuilder> inputMappings;

  /**
   * A list of ObjectBuilders defining the new annotations created by UIMA that
   * should be mapped back into GATE.
   */
  private List<GateAnnotationBuilder> outputsAdded;

  /**
   * A list of ObjectBuilders defining the annotations whose features have been
   * updated by UIMA, and for which changes should be propagated back into
   * GATE.
   */
  private List<GateAnnotationBuilder> outputsUpdated;

  /**
   * A list of ObjectBuilders giving the annotations that have been removed by
   * UIMA and for which the corresponding annotations should be removed in
   * GATE.
   */
  private List<GateAnnotationBuilder> outputsRemoved;


  ////// variables for the GATE/UIMA index //////

  /**
   * Feature Structure Type for the AnnotationSource FS type used for the
   * GATE/UIMA index.
   */
  private Type annotationSourceType;

  private static final String ANNOTATIONSOURCE_TYPE_NAME =
    "gate.uima.mapping.AnnotationSource";

  private Feature annotationSource_UIMAAnnotationFeature;

  private static final String ANNOTATIONSOURCE_UIMAANNOTATION_FEATURE_NAME =
    ANNOTATIONSOURCE_TYPE_NAME + ":UIMAAnnotation";

  private Feature annotationSource_GATEAnnotationIDFeature;

  private static final String ANNOTATIONSOURCE_GATEANNOTATIONID_FEATURE_NAME =
    ANNOTATIONSOURCE_TYPE_NAME + ":GATEAnnotationID";

  private Feature annotationSource_GATEAnnotationTypeFeature;

  private static final String ANNOTATIONSOURCE_GATEANNOTATIONTYPE_FEATURE_NAME =
    ANNOTATIONSOURCE_TYPE_NAME + ":GATEAnnotationType";

  private FSIndex<FeatureStructure> gateFSIndex;

  private static final String GATE_INDEX_LABEL = "GATEIndex";

  private FeaturePath gateAnnotationTypePath;

  /**
   * Initialise this resource.  This method creates the underlying UIMA objects
   * from their XML descriptor and parses the mapping definition.
   */
  public gate.Resource init() throws ResourceInstantiationException {
    // Sanity check on parameters - AE descriptor must be a non-null file: URL
    if(analysisEngineDescriptor == null) {
      throw new ResourceInstantiationException(
          "Analysis engine descriptor location must be specified");
    }
    if(!analysisEngineDescriptor.getProtocol().equals("file")) {
      throw new ResourceInstantiationException(
          "Analysis engine descriptor location must be a file: URL");
    }
    
    // mapping descriptor must be non-null
    if(mappingDescriptor == null) {
      throw new ResourceInstantiationException(
          "Annotation mapping descriptor must be specified");
    }

    // parse the uima descriptor and create the AE
    try {
      URI aeDescriptorURI =
        URI.create(analysisEngineDescriptor.toExternalForm());
      File aeDescriptorDir = new File(aeDescriptorURI).getParentFile();

      XMLInputSource aeDescriptorSource =
        new XMLInputSource(analysisEngineDescriptor.openStream(),
                           aeDescriptorDir);

      XMLParser uimaXMLParser = UIMAFramework.getXMLParser();
      // use more general type to allow for remote services
      //TaeDescription taeDescription =
      //  uimaXMLParser.parseTaeDescription(aeDescriptorSource);
      ResourceSpecifier taeDescription =
        uimaXMLParser.parseResourceSpecifier(aeDescriptorSource);

      analysisEngine = UIMAFramework.produceAnalysisEngine(taeDescription);

      // load our GATE-specific type system and index information
      XMLInputSource gateIndexSource = new XMLInputSource(
          this.getClass().getResourceAsStream("gateIndexTypeDefinition.xml"),
          new File(""));
      ResourceMetaData gateIndexDescription =
        uimaXMLParser.parseResourceMetaData(gateIndexSource);
      
      // create a CAS to use for the analysis engine and the GATE/UIMA index.
      // CAS instances are expensive to create, so we reuse the same tcas for
      // all documents.
      List<ResourceMetaData> casSpecs = Arrays.asList(new ResourceMetaData[] {
           analysisEngine.getAnalysisEngineMetaData(),
           gateIndexDescription});

      //tcas = analysisEngine.newTCAS();
      cas = CasCreationUtils.createCas(casSpecs);
    }
    catch(IOException ioe) {
      throw new ResourceInstantiationException(ioe);
    }
    catch(InvalidXMLException ixe) {
      // error in the TAE descriptor
      throw new ResourceInstantiationException(ixe);
    }
    catch(ResourceInitializationException rie) {
      // error creating TAE
      throw new ResourceInstantiationException(rie);
    }

    // parse the mapping file somehow
    SAXBuilder builder = new SAXBuilder();
    builder.setErrorHandler(new ErrorHandler() {
      public void warning(SAXParseException ex) {
        // do nothing on warnings
      }

      // treat all errors as fatal
      public void error(SAXParseException ex) throws SAXException {
        throw ex;
      }

      public void fatalError(SAXParseException ex) throws SAXException {
        throw ex;
      }
    });

    org.jdom.Document configDoc = null;

    try {
      configDoc = builder.build(mappingDescriptor);
    }
    catch(JDOMException jde) {
      throw (ResourceInstantiationException)
        new ResourceInstantiationException("Error parsing mapping file")
        .initCause(jde);
    }
    catch(IOException ioe) {
      throw (ResourceInstantiationException)
        new ResourceInstantiationException("Error reading mapping file")
        .initCause(ioe);
    }

    processMappingDescriptor(configDoc, cas.getTypeSystem());

    initUimaGateIndex(cas.getTypeSystem());

    return this;
  }

  /**
   * Executes the contained UIMA analysis engine, mapping the annotations to
   * and from the GATE document as defined by the mapping descriptor.
   */
  public void execute() throws ExecutionException {
    // trick to make sure the finally block doesn't hide exceptions that
    // happened further up
    boolean exceptionThrown = true;
    try {
      // populate the CAS with the text and input annotations according to
      // mapping
      cas.setDocumentText(document.getContent().toString());
      mapInputAnnotations();

      if(DEBUG) {
        File logfile = new File("casBefore.xml");
        try {
          FileOutputStream fos = new FileOutputStream(logfile);
          XCASSerializer.serialize(cas, fos);
          fos.close();
        }
        catch(Exception ex) {
          ex.printStackTrace();
        }
      }
      
      // run the AE
      @SuppressWarnings("unused")
      ProcessTrace trace = analysisEngine.process(cas);

      if(DEBUG) {
      /*  FSIndex annIndex = tcas.getAnnotationIndex();
        FSIterator it = annIndex.iterator();
        System.out.println("Dumping all annotations from CAS:");
        while(it.hasNext()) {
          Object obj = it.next();
          Class clz = obj.getClass();
          while(clz != null) {
            System.out.print(clz.toString() + Arrays.asList(clz.getInterfaces()) + "<-");
            clz = clz.getSuperclass();
          }
          System.out.println(obj);
        }*/
        File logfile = new File("casAfter.xml");
        try {
          FileOutputStream fos = new FileOutputStream(logfile);
          XCASSerializer.serialize(cas, fos);
          fos.close();
        }
        catch(Exception ex) {
          ex.printStackTrace();
        }
      }

      // compute the differences and map outputs back into document
      mapOutputs();

      exceptionThrown = false;
    }
    catch(AnalysisEngineProcessException aepe) {
      throw new ExecutionException(aepe);
    }
    catch(CASRuntimeException tre) {
      throw new ExecutionException(tre);
    }
    finally {
      try {
        // clear out the CAS ready for the next document
        cas.reset();
        clearIndexes();
      }
      catch(CASRuntimeException cre) {
        // oh well, we tried - only rethrow this exception if there isn't a
        // higher level one that we would mask
        if(!exceptionThrown) {
          throw new ExecutionException(cre);
        }
      }
    }
  }

  /**
   * Clean up the AnalysisEngine and CAS.
   */
  public void cleanup() {
    super.cleanup();
    // release the CAS
    cas.release();
    // clean up the analysis engine
    analysisEngine.destroy();
  }

  /**
   * Use the defined input mappings to populate the initial CAS.
   */
  private void mapInputAnnotations() throws ExecutionException {
    // nothing to do if there are no input mappings
    if(inputMappings == null || inputMappings.isEmpty()) {
      return;
    }

    // get the UIMA index repository, to which generated feature structures
    // will be added
    FSIndexRepository uimaIndexes = cas.getIndexRepository();
    if(uimaIndexes == null) {
      throw new ExecutionException("No index repository found for CAS - "
          + "there should be at least the AnnotationIndex");
    }

    // get the GATE annotation set that will be the source for GATE annotations
    // to map into UIMA
    AnnotationSet sourceSet = null;
    if(annotationSetName == null) {
      sourceSet = document.getAnnotations();
    }
    else {
      sourceSet = document.getAnnotations(annotationSetName);
    }

    Iterator<UIMAFeatureStructureBuilder> inputsIt = inputMappings.iterator();
    while(inputsIt.hasNext()) {
      UIMAFeatureStructureBuilder fsBuilder =
        inputsIt.next();

      if(fsBuilder instanceof UIMAAnnotationBuilder) {
        UIMAAnnotationBuilder annotBuilder = (UIMAAnnotationBuilder)fsBuilder;
        // if it's an annotation builder then call it once for each annotation
        // of the appropriate type

        // get all annotations of the appropriate type
        AnnotationSet annotsToMap =
          sourceSet.get(annotBuilder.getGateAnnotationType());

        if(annotsToMap != null) {
          Iterator<Annotation> annotsToMapIt = annotsToMap.iterator();
          while(annotsToMapIt.hasNext()) {
            gate.Annotation gateAnnot = annotsToMapIt.next();
            try {
              AnnotationFS uimaAnnot =
                (AnnotationFS)annotBuilder.buildObject(cas, document,
                                                       sourceSet, gateAnnot,
                                                       null);
              // add to UIMA index repository - this is important
              uimaIndexes.addFS(uimaAnnot);

              if(annotBuilder.isIndexed()) {
                addToUimaGateIndex(uimaAnnot, gateAnnot);
              }
            }
            catch(MappingException mx) {
              throw (ExecutionException)
                new ExecutionException("Error mapping input annotations")
                    .initCause(mx);
            }
          }
        }
      }
      else {
        // if it's not an annotation builder, just call it once and add the
        // result to the CAS
        try {
          FeatureStructure fs =
            (FeatureStructure)fsBuilder.buildObject(cas, document, sourceSet,
                                                    null, null);
          
          uimaIndexes.addFS(fs);
        }
        catch(MappingException mx) {
          throw (ExecutionException)
            new ExecutionException("Error mapping input annotations")
                .initCause(mx);
        }
      }
    }
  }

  /**
   * Use the output mappings to map changes in the UIMA annotations back into
   * GATE.
   */
  private void mapOutputs() throws ExecutionException {
    FSIndexRepository uimaIndexes = cas.getIndexRepository();
    if(uimaIndexes == null) {
      throw new ExecutionException("No index repository found for CAS - "
          + "there should be at least the AnnotationIndex");
    }

    // get the GATE annotation set that this PR operates on
    AnnotationSet annSet = null;
    if(annotationSetName == null) {
      annSet = document.getAnnotations();
    }
    else {
      annSet = document.getAnnotations(annotationSetName);
    }

    // added annotations
    if(!outputsAdded.isEmpty()) {
      Iterator<GateAnnotationBuilder> outputsAddedIt = outputsAdded.iterator();
      while(outputsAddedIt.hasNext()) {
        GateAnnotationBuilder outputBuilder =
          outputsAddedIt.next();

        // iterate over all the UIMA annotations of the appropriate type and
        // create GATE annotations to correspond
        Type uimaAnnotationType = outputBuilder.getUimaType();
        FSIndex<AnnotationFS> uimaIndex = cas.getAnnotationIndex(uimaAnnotationType);
        Iterator<AnnotationFS> uimaIndexIt = uimaIndex.iterator();
        while(uimaIndexIt.hasNext()) {
          FeatureStructure uimaAnn = uimaIndexIt.next();
          try {
            outputBuilder.buildObject(cas, document, annSet, null, uimaAnn);
          }
          catch(MappingException mx) {
            throw (ExecutionException)
              new ExecutionException("Error mapping output annotations")
              .initCause(mx);
          }
        }
      }
    }

    // updated annotations
    if(!outputsUpdated.isEmpty()) {
      Iterator<GateAnnotationBuilder> outputsUpdatedIt = outputsUpdated.iterator();
      while(outputsUpdatedIt.hasNext()) {
        GateAnnotationBuilder outputBuilder =
          outputsUpdatedIt.next();

        String gateAnnotType = outputBuilder.getGateType();

        // iterate over all the GATE annotations of the appropriate type, find
        // their corresponding UIMA annotations and update the GATE
        // annotation's features
        FSIterator<FeatureStructure> indexIt = getIndexIterator(gateAnnotType);
        while(indexIt.hasNext()) {
          FeatureStructure indexEntry = indexIt.next();
          if(DEBUG) {
            System.err.println("Updating outputs - index entry: " + indexEntry);
          }
          FeatureStructure uimaAnnot = getUIMAAnnotationFromIndex(indexEntry);
          Annotation gateAnnot = getGATEAnnotationFromIndex(indexEntry, annSet);
          try {
            outputBuilder.updateFeatures(cas, document, annSet, gateAnnot,
                uimaAnnot);
          }
          catch(MappingException mx) {
            throw (ExecutionException)
              new ExecutionException("Error mapping output annotations")
              .initCause(mx);
          }
        }
      }
    }

    // removed annotations
    if(!outputsRemoved.isEmpty()) {
      FSIndex<AnnotationFS> allAnnotationsIndex = cas.getAnnotationIndex();
      Iterator<GateAnnotationBuilder> outputsRemovedIt = outputsRemoved.iterator();
      while(outputsRemovedIt.hasNext()) {
        GateAnnotationBuilder outputBuilder =
          outputsRemovedIt.next();

        String gateAnnotType = outputBuilder.getGateType();

        // iterate over all the GATE annotations of the appropriate type, find
        // their corresponding UIMA annotations and update the GATE
        // annotation's features
        FSIterator<FeatureStructure> indexIt = getIndexIterator(gateAnnotType);
        INDEX_ENTRY: while(indexIt.hasNext()) {
          FeatureStructure indexEntry = indexIt.next();
          if(DEBUG) {
            System.err.println("\"removed\" output - index entry: " + indexEntry);
          }

          FeatureStructure uimaAnnot = getUIMAAnnotationFromIndex(indexEntry);
          Annotation gateAnnot = getGATEAnnotationFromIndex(indexEntry, annSet);
          // try and find uimaAnnot in the annotation index.  If it is not
          // there, it was removed by the TAE so remove the corresponding GATE
          // annotation.
          
          // We get an iterator that starts with the first feature structure
          // that is >= uimaAnnot under the AnnotationIndex ordering, i.e. the
          // first annotation that starts at the same place or to the right of
          // uimaAnnot
          FSIterator<AnnotationFS> annotIndexIt = allAnnotationsIndex.iterator(uimaAnnot);

          // now iterate starting from this location until either (a) we run
          // out of annotations in the AnnotationIndex, or (b) we come to an
          // annotation that is not equal to uimaAnnot under the index
          // ordering.
          while(annotIndexIt.isValid()
              && allAnnotationsIndex.compare(annotIndexIt.get(),
                                             uimaAnnot) == 0) {
            // check whether the current annotation from the AnnotationIndex is
            // actually equal to uimaAnnot.  If so, we have found uimaAnnot
            // still in the index, so we don't want to remove gateAnnot from
            // the GATE document.
            if(annotIndexIt.get().equals(uimaAnnot)) {
              continue INDEX_ENTRY;
            }

            annotIndexIt.moveToNext();
          }

          // if we get to here, we know that uimaAnnot is no longer in the
          // index, so remove its corresponding gateAnnot from the GATE
          // annotation set.
          annSet.remove(gateAnnot);

          // Whew! That was hard work.
        }
      }
    }
  }


  ///// GATE/UIMA annotation indexes /////

  /**
   * Initialise the necessary variables for the GATE/UIMA index.
   */
  private void initUimaGateIndex(TypeSystem typeSystem)
                    throws ResourceInstantiationException {
    annotationSourceType = typeSystem.getType(ANNOTATIONSOURCE_TYPE_NAME);
    if(annotationSourceType == null) {
      throw new ResourceInstantiationException("Could not find "
          + ANNOTATIONSOURCE_TYPE_NAME + " in type system");
    }

    annotationSource_UIMAAnnotationFeature = typeSystem.getFeatureByFullName(
        ANNOTATIONSOURCE_UIMAANNOTATION_FEATURE_NAME);
    if(annotationSource_UIMAAnnotationFeature == null) {
      throw new ResourceInstantiationException("Could not find feature "
          + ANNOTATIONSOURCE_UIMAANNOTATION_FEATURE_NAME + " in type system");
    }

    annotationSource_GATEAnnotationIDFeature = typeSystem.getFeatureByFullName(
        ANNOTATIONSOURCE_GATEANNOTATIONID_FEATURE_NAME);
    if(annotationSource_GATEAnnotationIDFeature == null) {
      throw new ResourceInstantiationException("Could not find feature "
          + ANNOTATIONSOURCE_GATEANNOTATIONID_FEATURE_NAME + " in type system");
    }

    annotationSource_GATEAnnotationTypeFeature =
      typeSystem.getFeatureByFullName(
        ANNOTATIONSOURCE_GATEANNOTATIONTYPE_FEATURE_NAME);
    if(annotationSource_GATEAnnotationTypeFeature == null) {
      throw new ResourceInstantiationException("Could not find feature "
          + ANNOTATIONSOURCE_GATEANNOTATIONTYPE_FEATURE_NAME
          + " in type system");
    }

    FSIndexRepository uimaIndexes = cas.getIndexRepository();
    gateFSIndex = uimaIndexes.getIndex(GATE_INDEX_LABEL);
    if(gateFSIndex == null) {
      throw new ResourceInstantiationException("Couldn't find GATE index "
          + "in UIMA index repository");
    }

    gateAnnotationTypePath = cas.createFeaturePath();
    gateAnnotationTypePath.addFeature(
        annotationSource_GATEAnnotationTypeFeature);
  }
  
  /**
   * Clear the indexes mapping GATE annotations to UIMA ones.
   */
  private void clearIndexes() {
    // nothing to do - the index is stored in the CAS, so will clear when the
    // CAS is reset
  }

  /**
   * Store a GATE/UIMA annotation pair in the index.
   */
  private void addToUimaGateIndex(AnnotationFS uimaAnnot,
                                  gate.Annotation gateAnnot) {
    //uimaGateIndex.put(uimaAnnot, gateAnnot.getId());
    FeatureStructure indexEntry = cas.createFS(annotationSourceType);
    indexEntry.setFeatureValue(annotationSource_UIMAAnnotationFeature,
        uimaAnnot);
    indexEntry.setIntValue(annotationSource_GATEAnnotationIDFeature,
        gateAnnot.getId().intValue());
    indexEntry.setStringValue(annotationSource_GATEAnnotationTypeFeature,
        gateAnnot.getType());
    cas.getIndexRepository().addFS(indexEntry);
    
    if(DEBUG) {
      System.out.println("Put annotation " + gateAnnot + " into index.");
    }
  }

  /**
   * Returns an FSIterator over the GATE/UIMA index for the index entries that
   * refer to the specified type of GATE annotation.
   */
  private FSIterator<FeatureStructure> getIndexIterator(String gateAnnotType) {
    ConstraintFactory cf = cas.getConstraintFactory();
    // construct a matching constraint to allow us to iterate over only
    // those index entries that refer to the right kind of GATE annotation
    FSStringConstraint annotTypeConstraint = cf.createStringConstraint();
    annotTypeConstraint.equals(gateAnnotType);

    FSMatchConstraint matchConstraint =
      cf.embedConstraint(gateAnnotationTypePath, annotTypeConstraint);

    FSIterator<FeatureStructure> allIndexEntriesIt = gateFSIndex.iterator();
    FSIterator<FeatureStructure> indexIt = cas.createFilteredIterator(
        allIndexEntriesIt, matchConstraint);

    return indexIt;
  }

  /**
   * Extract the UIMA annotation from an index entry.
   */
  private FeatureStructure getUIMAAnnotationFromIndex(
                                           FeatureStructure indexEntry) {
    return indexEntry.getFeatureValue(annotationSource_UIMAAnnotationFeature);
  }

  /**
   * Returns the GATE annotation from the given set referenced by the given
   * index entry.
   */
  private gate.Annotation getGATEAnnotationFromIndex(
                               FeatureStructure indexEntry, AnnotationSet as) {
    int gateID =
      indexEntry.getIntValue(annotationSource_GATEAnnotationIDFeature);
    return as.get(new Integer(gateID));
  }
  
  //////// processing the mapping descriptor ////////

  private void processMappingDescriptor(org.jdom.Document doc,
                                        TypeSystem typeSystem)
               throws ResourceInstantiationException {
    Element topElement = doc.getRootElement();
    // process input section
    Element inputsElement = topElement.getChild("inputs");
    inputMappings = new ArrayList<UIMAFeatureStructureBuilder>();

    if(inputsElement != null) {
      @SuppressWarnings("unchecked")
      List<Element> inputElements = (List<Element>)inputsElement.getChildren();
      Iterator<Element> inputMappingsIt = inputElements.iterator();
      while(inputMappingsIt.hasNext()) {
        Element mapping = inputMappingsIt.next();

        try {
          ObjectBuilder inputBuilder =
            ObjectManager.createBuilder(mapping, typeSystem);

          if(!(inputBuilder instanceof UIMAFeatureStructureBuilder)) {
            throw new ResourceInstantiationException(
                "input mapping must be a feature structure builder");
          }
          
          inputMappings.add((UIMAFeatureStructureBuilder)inputBuilder);
        }
        catch(MappingException mx) {
          throw (ResourceInstantiationException)
            new ResourceInstantiationException("Error creating input mapping")
              .initCause(mx);
        }
      }
    }

    // process outputs
    outputsAdded = new ArrayList<GateAnnotationBuilder>();
    outputsUpdated = new ArrayList<GateAnnotationBuilder>();
    outputsRemoved = new ArrayList<GateAnnotationBuilder>();

    Element outputsElement = topElement.getChild("outputs");
    if(outputsElement != null) {
      String[] elements = new String[] {"added", "updated", "removed"};
      List<List<GateAnnotationBuilder>> lists = Arrays.asList(outputsAdded, outputsUpdated, outputsRemoved);
      for(int i = 0; i < elements.length; i++) {
        Element elt = outputsElement.getChild(elements[i]);
        if(elt != null) {
          @SuppressWarnings("unchecked")
          List<Element> outputElements = (List<Element>)elt.getChildren();
          Iterator<Element> outputMappingsIt = outputElements.iterator();
          while(outputMappingsIt.hasNext()) {
            Element mapping = outputMappingsIt.next();
            
            try {
              ObjectBuilder outputBuilder =
                ObjectManager.createBuilder(mapping, typeSystem);

              if(!(outputBuilder instanceof GateAnnotationBuilder)) {
                throw new ResourceInstantiationException(
                    "output mapping must be a GATE annotation builder");
              }
              
              lists.get(i).add((GateAnnotationBuilder)outputBuilder);
            }
            catch(MappingException mx) {
              throw (ResourceInstantiationException)
                new ResourceInstantiationException(
                    "Error creating output mapping").initCause(mx);
            }
          }
        }
      }
    }
  }
}
