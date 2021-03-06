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
package gate.uima.mapping;

import java.util.*;
import java.io.InputStream;
import java.io.IOException;

import org.apache.uima.cas.TypeSystem;
import org.jdom.Element;

public class ObjectManager {
  /**
   * Helper class that should not be instantiated.
   */
  private ObjectManager() {
  }

  private static Map<String, Class<? extends ObjectBuilder>> elementNameToClass = null;

  private static synchronized void init() throws MappingException {
    // return if already inited
    if(elementNameToClass != null) {
      return;
    }

    Map<String, Class<? extends ObjectBuilder>> elementNameMap = new HashMap<>();

    Properties builderClasses = new Properties();
    try(InputStream propsStream =
        ObjectManager.class.getResourceAsStream("objectbuilders.properties")) {
      builderClasses.load(propsStream);
    }
    catch(IOException ioe) {
      throw new MappingException("Couldn't load objectbuilders.properties");
    }

    // file format is elementName=className
    Iterator<Map.Entry<Object, Object>> buildersIt = builderClasses.entrySet().iterator();
    while(buildersIt.hasNext()) {
      Map.Entry<Object, Object> builder = buildersIt.next();
      try {
        Class<? extends ObjectBuilder> builderClass = Class.forName((String)builder.getValue())
            .asSubclass(ObjectBuilder.class);
        elementNameMap.put((String)builder.getKey(), builderClass);
      }
      catch(ClassNotFoundException cnfe) {
        throw new MappingException("Couldn't load builder class "
            + builder.getValue(), cnfe);
      }
    }

    // store complete map
    elementNameToClass = elementNameMap;
  }

  /**
   * Create an object builder appropriate to the given XML element, and
   * initialise it with the given type system.
   */
  public static ObjectBuilder createBuilder(Element elt, TypeSystem typeSystem)
          throws MappingException {
    // load builder definitions, if necessary
    if(elementNameToClass == null) {
      init();
    }

    String elementName = elt.getName();
    Class<? extends ObjectBuilder> builderClass = elementNameToClass.get(elementName);
    if(builderClass == null) {
      throw new MappingException("Unrecognised element name " + elementName);
    }

    ObjectBuilder builder = null;
    try {
      builder = builderClass.newInstance();
    }
    catch(IllegalAccessException iae) {
      throw new MappingException("Couldn't access class "
          + builderClass.getName(), iae);
    }
    catch(InstantiationException ie) {
      throw new MappingException("Couldn't instantiate builder class "
          + builderClass.getName(), ie);
    }

    builder.configure(elt, typeSystem);
    return builder;
  }
}
