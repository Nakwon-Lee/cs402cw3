::#set java 7 as JAVA_HOME
::#JAVA_HOME = "your java 7 home"
java -cp soot-trunk.jar soot.Main -cp .;"%JAVA_HOME%\jre\lib\rt.jar" -output-dir . -output-format shimple -print-tags -keep-line-number -p jb use-original-names:true %1
