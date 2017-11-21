package gate.corpora.export;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.apache.uima.UIMAFramework;
import org.apache.uima.cas.CAS;
import org.apache.uima.cas.CASRuntimeException;
import org.apache.uima.cas.FSIndexRepository;
import org.apache.uima.cas.FeatureStructure;
import org.apache.uima.cas.TypeSystem;
import org.apache.uima.cas.impl.XCASSerializer;
import org.apache.uima.cas.text.AnnotationFS;
import org.apache.uima.resource.ResourceInitializationException;
import org.apache.uima.resource.metadata.MetaDataObject;
import org.apache.uima.resource.metadata.ResourceMetaData;
import org.apache.uima.util.CasCreationUtils;
import org.apache.uima.util.InvalidXMLException;
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
import gate.Document;
import gate.DocumentExporter;
import gate.Factory;
import gate.FeatureMap;
import gate.Gate;
import gate.LanguageAnalyser;
import gate.creole.ExecutionException;
import gate.creole.Plugin;
import gate.creole.ResourceInstantiationException;
import gate.creole.metadata.AutoInstance;
import gate.creole.metadata.CreoleParameter;
import gate.creole.metadata.CreoleResource;
import gate.creole.metadata.RunTime;
import gate.uima.mapping.MappingException;
import gate.uima.mapping.ObjectBuilder;
import gate.uima.mapping.ObjectManager;
import gate.uima.mapping.UIMAAnnotationBuilder;
import gate.uima.mapping.UIMAFeatureStructureBuilder;

@CreoleResource(name = "UIMA CAS XMI Exporter", tool = true, autoinstances = @AutoInstance)
public class UIMACASXMIExporter extends DocumentExporter {

  private static final long serialVersionUID = 8980467635623023999L;

  private URL typeSystemURL, mappingDescriptorURL;
  
  public URL getTypeSystemURL() {
    return typeSystemURL;
  }
  
  @RunTime
  @CreoleParameter
  public void setTypeSystemURL(URL typeSystemURL) {
    this.typeSystemURL = typeSystemURL;
  }
  
  public URL getMappingDescriptorURL() {
    return mappingDescriptorURL;
  }
  
  @RunTime
  @CreoleParameter
  public void setMappingDescriptorURL(URL mappingDescriptorURL) {
    this.mappingDescriptorURL = mappingDescriptorURL;
  }
  
  public UIMACASXMIExporter() {
    // need to check that the mimetype is definitely right
    super("UIMA CAS XMI", "xml", "application/vnd.xmi+xml");
  }

  @Override
  public void export(Document doc, OutputStream out, FeatureMap options)
      throws IOException {

    // get the GATE annotation set that will be the source for GATE annotations
    // to map into UIMA
    /*
     * AnnotationSet sourceSet = null; if(annotationSetName == null) { sourceSet
     * = document.getAnnotations(); } else { sourceSet =
     * document.getAnnotations(annotationSetName); }
     */
    try {
      CAS cas = null;

      XMLParser uimaXMLParser = UIMAFramework.getXMLParser();
      
      XMLInputSource typeSystemSource = new XMLInputSource((URL)options.get("typesystem"));
      ResourceMetaData typeSystem =
        uimaXMLParser.parseResourceMetaData(typeSystemSource);
      
      cas = CasCreationUtils
          .createCas(Arrays.asList(new MetaDataObject[]{typeSystem}));

      cas.setDocumentText(doc.getContent().toString());

      AnnotationSet sourceSet =
          doc.getAnnotations((String)options.get("annotationSetName"));

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

      org.jdom.Document configDoc =
          builder.build((URL)options.get("mappingDescriptor"));

      List<UIMAFeatureStructureBuilder> inputMappings =
          processMappingDescriptor(configDoc, cas.getTypeSystem());

      mapInputAnnotations(cas, doc, sourceSet, inputMappings);

      XCASSerializer.serialize(cas, out);

    } catch(ExecutionException | SAXException | ResourceInitializationException
        | CASRuntimeException | ResourceInstantiationException | JDOMException
        | InvalidXMLException e) {
      throw new IOException(e);
    }
  }

  /**
   * Use the defined input mappings to populate the initial CAS.
   */
  private void mapInputAnnotations(CAS cas, Document document,
      AnnotationSet sourceSet, List<UIMAFeatureStructureBuilder> inputMappings)
      throws ExecutionException {
    // nothing to do if there are no input mappings
    if(inputMappings == null || inputMappings.isEmpty()) { return; }

    // get the UIMA index repository, to which generated feature structures
    // will be added
    FSIndexRepository uimaIndexes = cas.getIndexRepository();
    if(uimaIndexes == null) { throw new ExecutionException(
        "No index repository found for CAS - "
            + "there should be at least the AnnotationIndex"); }

    Iterator<UIMAFeatureStructureBuilder> inputsIt = inputMappings.iterator();
    while(inputsIt.hasNext()) {
      UIMAFeatureStructureBuilder fsBuilder = inputsIt.next();

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
            Annotation gateAnnot = annotsToMapIt.next();
            try {
              AnnotationFS uimaAnnot = (AnnotationFS)annotBuilder
                  .buildObject(cas, document, sourceSet, gateAnnot, null);
              // add to UIMA index repository - this is important
              uimaIndexes.addFS(uimaAnnot);

              // we aren't going to try and do anything clever loading the stuff
              // back..... yet, so just ignore this for now
              /*
               * if(annotBuilder.isIndexed()) { addToUimaGateIndex(uimaAnnot,
               * gateAnnot); }
               */
            } catch(MappingException mx) {
              throw (ExecutionException)new ExecutionException(
                  "Error mapping input annotations").initCause(mx);
            }
          }
        }
      } else {
        // if it's not an annotation builder, just call it once and add the
        // result to the CAS
        try {
          FeatureStructure fs = (FeatureStructure)fsBuilder.buildObject(cas,
              document, sourceSet, null, null);

          uimaIndexes.addFS(fs);
        } catch(MappingException mx) {
          throw (ExecutionException)new ExecutionException(
              "Error mapping input annotations").initCause(mx);
        }
      }
    }
  }

  private List<UIMAFeatureStructureBuilder> processMappingDescriptor(
      org.jdom.Document doc, TypeSystem typeSystem)
      throws ResourceInstantiationException {
    Element topElement = doc.getRootElement();
    // process input section
    Element inputsElement = topElement.getChild("inputs");
    List<UIMAFeatureStructureBuilder> inputMappings =
        new ArrayList<UIMAFeatureStructureBuilder>();

    if(inputsElement != null) {
      List inputElements = inputsElement.getChildren();
      Iterator inputMappingsIt = inputElements.iterator();
      while(inputMappingsIt.hasNext()) {
        Element mapping = (Element)inputMappingsIt.next();

        try {
          ObjectBuilder inputBuilder =
              ObjectManager.createBuilder(mapping, typeSystem);

          if(!(inputBuilder instanceof UIMAFeatureStructureBuilder)) { throw new ResourceInstantiationException(
              "input mapping must be a feature structure builder"); }

          inputMappings.add((UIMAFeatureStructureBuilder)inputBuilder);
        } catch(MappingException mx) {
          throw (ResourceInstantiationException)new ResourceInstantiationException(
              "Error creating input mapping").initCause(mx);
        }
      }
    }

    return inputMappings;
  }

  public static void main(String args[]) throws Exception {
    Gate.init();
    Gate.getCreoleRegister()
        .registerPlugin(new Plugin.Component(UIMACASXMIExporter.class));

    Gate.getCreoleRegister().registerPlugin(new Plugin.Maven("uk.ac.gate.plugins", "annie", "8.5-SNAPSHOT"));
    
    Document doc = Factory.newDocument("Hello World");
    
    LanguageAnalyser tokenizer = (LanguageAnalyser)Factory.createResource("gate.creole.tokeniser.DefaultTokeniser");
    
    tokenizer.setDocument(doc);
    tokenizer.execute();
    
    //System.out.println(doc);

    DocumentExporter exporter =
        DocumentExporter.getInstance(UIMACASXMIExporter.class.getName());

    FeatureMap params = Factory.newFeatureMap();
    params.put("mappingDescriptor",
        (new File("./examples/conf/mapping/TokenHandlerGateMapping.xml").toURI()
            .toURL()));

    params.put("typesystem",
        (new File("./typesystem.xml"))
            .toURI().toURL());

    exporter.export(doc, System.out, params);
  }
}
