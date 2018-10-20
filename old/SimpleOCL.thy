theory SimpleOCL
  imports Main
begin

datatype OclBoolExp = OclBoolLiteral bool
  | OclNotExp OclBoolExp
  | OclAndExp OclBoolExp OclBoolExp
  | OclOrExp OclBoolExp OclBoolExp
  | OclImpliesExp OclBoolExp OclBoolExp

primrec "OclBoolExpValue" :: "OclBoolExp \<Rightarrow> bool"
  where
    "OclBoolExpValue (OclBoolLiteral a) = a" |
    "OclBoolExpValue (OclNotExp a) = (\<not> OclBoolExpValue a)" |
    "OclBoolExpValue (OclAndExp a b) = (OclBoolExpValue a \<and> OclBoolExpValue b)" |
    "OclBoolExpValue (OclOrExp a b) = (OclBoolExpValue a \<or> OclBoolExpValue b)" |
    "OclBoolExpValue (OclImpliesExp a b) = (OclBoolExpValue a \<longrightarrow> OclBoolExpValue b)"

datatype XPathBoolExp = XPathBoolLiteral bool
  | XPathNotExp XPathBoolExp
  | XPathAndExp XPathBoolExp XPathBoolExp
  | XPathOrExp XPathBoolExp XPathBoolExp

primrec "XPathBoolExpValue" :: "XPathBoolExp \<Rightarrow> bool"
  where
    "XPathBoolExpValue (XPathBoolLiteral a) = a" |
    "XPathBoolExpValue (XPathNotExp a) = (\<not> XPathBoolExpValue a)" |
    "XPathBoolExpValue (XPathAndExp a b) = (XPathBoolExpValue a \<and> XPathBoolExpValue b)" |
    "XPathBoolExpValue (XPathOrExp a b) = (XPathBoolExpValue a \<or> XPathBoolExpValue b)"

primrec "OclToXPath" :: "OclBoolExp \<Rightarrow> XPathBoolExp"
  where
    "OclToXPath (OclBoolLiteral a) = XPathBoolLiteral a" |
    "OclToXPath (OclNotExp a) = XPathNotExp (OclToXPath a)" |
    "OclToXPath (OclAndExp a b) = XPathAndExp (OclToXPath a) (OclToXPath b)" |
    "OclToXPath (OclOrExp a b) = XPathOrExp (OclToXPath a) (OclToXPath b)" |
    "OclToXPath (OclImpliesExp a b) = XPathOrExp (XPathNotExp (OclToXPath a)) (OclToXPath b)"

lemma OclToXPathRight: "OclBoolExpValue a = XPathBoolExpValue (OclToXPath a)"
  apply (induct a)
  apply simp_all
  done

end
