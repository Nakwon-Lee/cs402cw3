#!/bin/bash
#set java 7 as JAVA_HOME
JAVA_HOME=/usr/lib/jvm/java-7-oracle
java -cp ./soot-trunk.jar soot.Main -cp .:$JAVA_HOME/jre/lib/rt.jar -output-dir . -output-format shimple -print-tags -keep-line-number -p jb use-original-names:true $@
