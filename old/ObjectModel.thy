theory ObjectModel
  imports Main
    "~~/src/HOL/Library/Extended_Nat"
    "~~/src/HOL/Library/Finite_Map"
begin

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)

definition denorm :: "('a \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> ('a \<times> 'b) fset" where
  "denorm m \<equiv> (\<lambda> k. (k, the (fmlookup m k))) |`| fmdom m"

definition flatten :: "('a \<times> 'b fset) fset \<Rightarrow> ('a \<times> 'b) fset" where
  "flatten s \<equiv> ffUnion ((\<lambda>(x,y). (\<lambda>z. (x,z)) |`| y) |`| s)"

definition denorm3 :: "('a \<rightharpoonup>\<^sub>f 'b \<rightharpoonup>\<^sub>f 'c) \<Rightarrow> ('a \<times> 'b \<times> 'c) fset" where
  "denorm3 m \<equiv> flatten ((\<lambda>k. (k, denorm (the (fmlookup m k)))) |`| fmdom m)"

(* Kinds *)

type_synonym cls = "string"
type_synonym attr = "string"
type_synonym assoc = "string"
type_synonym role = "string"
type_synonym oid = "string"

(* Type System *)

datatype type = AnyType | VoidType | IntegerType | StringType | Class cls
datatype val = IntegerValue int | StringValue string | VoidValue | ObjectValue cls oid

fun type_of_val :: "val \<Rightarrow> type" where
  "type_of_val (VoidValue) = VoidType"
| "type_of_val (IntegerValue _) = IntegerType"
| "type_of_val (StringValue _) = StringType"
| "type_of_val (ObjectValue cls _) = Class cls"

(* Model *)

type_synonym class_set = "cls fset"
type_synonym attrs = "cls \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f type"
type_synonym assoc_end = "cls \<times> role \<times> nat \<times> enat"
type_synonym assocs = "assoc \<rightharpoonup>\<^sub>f assoc_end list"
type_synonym model = "class_set \<times> attrs \<times> assocs"

definition assoc_end_class :: "assoc_end \<Rightarrow> cls" where
  "assoc_end_class \<equiv> fst"

definition assoc_end_role :: "assoc_end \<Rightarrow> role" where
  "assoc_end_role \<equiv> fst \<circ> snd"

definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd \<circ> snd"

definition assoc_end_min_le_max :: "assoc_end \<Rightarrow> bool" where
  "assoc_end_min_le_max x \<equiv> assoc_end_min x \<le> assoc_end_max x"

definition assoc_classes :: "assoc_end list \<Rightarrow> cls fset" where
  "assoc_classes \<equiv> fset_of_list \<circ> (map assoc_end_class)"

definition assoc_roles_distinct :: "assoc_end list \<Rightarrow> bool" where
  "assoc_roles_distinct \<equiv> distinct \<circ> (map assoc_end_role)"

definition assoc_is_ok :: "assoc_end list \<Rightarrow> bool" where
  "assoc_is_ok assoc \<equiv> assoc_roles_distinct assoc \<and> list_all assoc_end_min_le_max assoc"

inductive model_is_ok :: "model \<Rightarrow> bool" where
  "\<comment> \<open>Attributes defined for existing classes\<close>
   fmdom attrs |\<subseteq>| classes \<Longrightarrow>
   \<comment> \<open>Associations defined for existing classes\<close>
   fBall (fmran assocs) (\<lambda>x. assoc_classes x |\<subseteq>| classes) \<Longrightarrow>
   \<comment> \<open>Associations have distinct role names and min \<le> max\<close>
   fBall (fmran assocs) assoc_is_ok \<Longrightarrow>
   model_is_ok (classes, attrs, assocs)"

code_pred [show_modes] model_is_ok .

(* Data *)

type_synonym objects = "oid \<rightharpoonup>\<^sub>f cls"
type_synonym attr_vals = "oid \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f val"
type_synonym links = "assoc \<rightharpoonup>\<^sub>f oid list"
type_synonym data = "objects \<times> attr_vals \<times> links"

inductive data_is_ok :: "data \<Rightarrow> bool" where
  "\<comment> \<open>Attribute values defined for existing objects\<close>
   fmdom attr_vals |\<subseteq>| fmdom objects \<Longrightarrow>
   \<comment> \<open>Links defined for existing objects\<close>
   fBall (fmran links) (\<lambda>x. fset_of_list x |\<subseteq>| fmdom objects) \<Longrightarrow>
   data_is_ok (objects, attr_vals, links)"

code_pred [show_modes] data_is_ok .

(*
Количество ссылок в ассоциации правильное
Количество связей правильное
*)
definition attr_vals_signature :: "objects \<Rightarrow> oid \<times> attr \<times> val \<Rightarrow> cls \<times> attr \<times> type" where
  "attr_vals_signature objects \<equiv> \<lambda>(obj, a, v). (the (fmlookup objects obj), a, type_of_val v)"
(*
definition attr_vals_is_ok where
  "attr_vals_is_ok objects attr_vals attrs \<equiv> fBall (fmdom attr_vals) (\<lambda>obj.
    (case (fmlookup objects obj) of Some cls \<Rightarrow>
      (case (fmlookup attr_vals obj) of Some vals \<Rightarrow>
        (case (fmlookup attrs cls) of Some cls_attrs \<Rightarrow>
          fBall (fmdom vals) (\<lambda>prop.
            (case (fmlookup vals prop, fmlookup cls_attrs prop) of (Some v, Some \<tau>) \<Rightarrow>
              type_of_val v = \<tau>
            | _ \<Rightarrow> False))
        | _ \<Rightarrow> False)
      | _ \<Rightarrow> True)
    | _ \<Rightarrow> False))"
*)
definition attr_vals_is_ok2 where
  "attr_vals_is_ok2 cls_attrs vals \<equiv>
    fBall (fmdom cls_attrs |\<union>| fmdom vals) (\<lambda>prop.
      case (fmlookup cls_attrs prop, fmlookup vals prop)
        of (Some \<tau>, Some v) \<Rightarrow> type_of_val v = \<tau>
         | (_, _) \<Rightarrow> False)"

definition attr_vals_is_ok where
  "attr_vals_is_ok attrs objects attr_vals \<equiv>
    fBall (fmdom objects) (\<lambda>obj.
      case (fmlookup objects obj) of Some cls \<Rightarrow>
        case (fmlookup attrs cls, fmlookup attr_vals obj)
          of (None, None) \<Rightarrow> True
           | (None, Some _) \<Rightarrow> False
           | (Some _, None) \<Rightarrow> False
           | (Some cls_attrs, Some vals) \<Rightarrow>
                attr_vals_is_ok2 cls_attrs vals)"

inductive conforms_to_model :: "model \<Rightarrow> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "model_is_ok model \<Longrightarrow>
   data_is_ok data \<Longrightarrow>
   model = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   (* Objects belong to existing classes *)
   fmran objects |\<subseteq>| classes \<Longrightarrow>
   (* Links defined for existing associations *)
   fmdom links |\<subseteq>| fmdom assocs \<Longrightarrow>
   (* Attribute values defined for existing attributes and have right types *)
   attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
(*
   (\<forall>obj.
     fmlookup objects obj = Some cls \<Longrightarrow>
     fmlookup attr_vals obj = Some vals \<Longrightarrow>
     \<exists>cls_attrs.
        fmlookup attrs cls = Some cls_attrs \<and>
        (\<forall>prop.
          fmlookup vals prop = Some v \<and>
          fmlookup cls_attrs prop = Some t)) \<Longrightarrow>
*)
(*   attrs_set = denorm3 attrs \<Longrightarrow>
   attrs_set' = attr_vals_signature objects |`| denorm3 attr_vals \<Longrightarrow>
   attrs_set' |\<subseteq>| attrs_set \<Longrightarrow>*)
   model \<turnstile> data"


code_pred [show_modes] conforms_to_model .

(*
lemma q:
  "attrs_set = denorm3 attrs \<Longrightarrow>
   attrs_set' = attr_vals_signature objects |`| denorm3 attr_vals \<Longrightarrow>
   attrs_set' |\<subseteq>| attrs_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   "
*)

lemma attr_vals_is_ok_then:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   attr_vals_is_ok2 cls_attrs vals"
  apply (simp add: attr_vals_is_ok_def)
  by (metis (no_types, lifting) case_prodD fBall_alt_def fmlookup_dom_iff option.simps(5))

lemma attr_vals_is_ok_then2:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdomI option.simps(5))

lemma attr_vals_is_ok_then_rev:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   \<exists>cls_attrs vals.
      fmlookup attrs cls = None \<and>
      fmlookup attr_vals obj = None \<or>
      fmlookup attrs cls = Some cls_attrs \<and>
      fmlookup attr_vals obj = Some vals"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then_rev2:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
    (\<exists>cls_attrs. fmlookup attrs cls = Some cls_attrs) \<longleftrightarrow>
    (\<exists>vals. fmlookup attr_vals obj = Some vals)"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then2_rev:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<or>
   fmlookup vals prop = Some v \<Longrightarrow>
   \<exists>\<tau> v.
    fmlookup cls_attrs prop = Some \<tau> \<and>
    fmlookup vals prop = Some v \<and>
    type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdom_notD fmlookup_dom_iff option.case_eq_if option.sel)

lemma model_preserv_type:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2)
  (*apply (simp add: attr_vals_is_ok_def)
  by (smt attr_vals_is_ok2_def case_prodD fbspec fmdom_notD option.discI option.simps(5))*)

lemma q:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   \<exists>vals v.
      fmlookup attr_vals obj = Some vals \<and>
      fmlookup vals prop = Some v"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2_rev attr_vals_is_ok_then_rev fmdomI fmdom_notI)

lemma q:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   type_of_val (ObjectVal cls obj) = ObjectType cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   \<exists>vals v.
      fmlookup objects obj = Some cls \<and>
      fmlookup attr_vals obj = Some vals \<and>
      fmlookup vals prop = Some v"


lemma q:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   \<exists>vals v.
     fmlookup objects obj = Some cls \<and>
     fmlookup attr_vals obj = Some vals \<and>
     fmlookup vals prop = Some v"
  apply (simp add: attr_vals_is_ok_def)




lemma q:
  "(*\<M> = (classes, attrs, assocs) \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   \<M> \<turnstile> d \<Longrightarrow>*)
   (*type_of_val (ObjectVal cls obj) = ObjectType cls \<Longrightarrow>*)
   attr_vals_is_ok objects attr_vals attrs \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>*)

   (*obj |\<in>| fmdom attr_vals \<Longrightarrow>*)
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>*)
   (*fmlookup attr_vals obj = Some vals \<Longrightarrow>*)
   \<exists>vals cls_attrs.
     fmlookup attr_vals obj = Some vals \<and>
     fmlookup attrs cls = Some cls_attrs
     (*fmlookup vals prop = Some v*)"
  apply (simp add: attr_vals_is_ok_def)
  apply (smt fbspec fmdomI option.case_eq_if option.collapse option.sel)
  done

lemma q2:
  "(*\<M> = (classes, attrs, assocs) \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   \<M> \<turnstile> d \<Longrightarrow>*)
   (*type_of_val (ObjectVal cls obj) = ObjectType cls \<Longrightarrow>*)
   attr_vals_is_ok2 vals cls_attrs \<Longrightarrow>
   prop |\<in>| fmdom vals \<Longrightarrow>
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>*)

   (*obj |\<in>| fmdom attr_vals \<Longrightarrow>*)
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>*)
   (*fmlookup attr_vals obj = Some vals \<Longrightarrow>*)
   \<exists>v \<tau>.
     fmlookup vals prop = Some v \<and>
     fmlookup cls_attrs prop = Some \<tau>
     (*fmlookup vals prop = Some v*)"
  apply (simp add: attr_vals_is_ok2_def)
  apply (smt fbspec fmlookup_dom_iff option.case_eq_if option.collapse)
  done

lemma q:
  "(*\<M> = (classes, attrs, assocs) \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   \<M> \<turnstile> d \<Longrightarrow>*)
   (*type_of_val (ObjectVal cls obj) = ObjectType cls \<Longrightarrow>*)
   attr_vals_is_ok objects attr_vals attrs \<Longrightarrow>
   obj |\<in>| fmdom attr_vals \<Longrightarrow>
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>*)
   \<exists>v vals.
     fmlookup attr_vals obj = Some vals \<and>
     fmlookup vals prop = Some v"
  apply (simp add: attr_vals_is_ok_def)
  apply (simp add: fmlookup_dom_iff)
  done


(*
"Abs_fset
  {(''Company'', ''name'', StringType), (''Car'', ''power'', IntegerType), (''Car'', ''color'', StringType),
   (''Person'', ''name'', StringType)}"
  :: "(char list \<times> char list \<times> ObjectModel.type) fset"
"Abs_fset {(''Car1'', ''color'', StringValue ''White''), (''Ivan'', ''name'', StringValue ''Ivan'')}"
  :: "(char list \<times> char list \<times> val) fset"
*)

(* Example *)

definition classes1 :: "cls fset" where
  "classes1 \<equiv> {|''Person'',''Car'',''Company''|}"

definition attrs1 :: "attrs" where
  "attrs1 = fmap_of_list [
    (''Person'', fmap_of_list [
      (''name'', StringType)]),
    (''Car'', fmap_of_list [
      (''color'', StringType),
      (''power'', IntegerType)]),
    (''Company'', fmap_of_list [
      (''name'', StringType)])]"

definition assocs1 :: "assocs" where
  "assocs1 \<equiv> fmap_of_list [
    (''PersonCar'', [
      (''Person'',''Driver'',1,1),
      (''Car'',''Car'',1,3)]),
    (''Employment'', [
      (''Company'',''Company'',0,2),
      (''Person'',''Employee'',1,\<infinity>)])]"

definition model1 :: "model" where
  "model1 \<equiv> (classes1, attrs1, assocs1)"

term "model1"

definition objects1 :: "objects" where
  "objects1 \<equiv> fmap_of_list [
    (''Ivan'', ''Person''),
    (''Jhon'', ''Person''),
    (''Car1'', ''Car''),
    (''Car2'', ''Car''),
    (''Car3'', ''Car'')]"

definition attr_val1 :: "attr_vals" where
  "attr_val1 \<equiv> fmap_of_list [
    (''Ivan'', fmap_of_list [
      (''name'', StringValue ''Ivan'')]),
      (*(''name'', IntegerValue 1)]),*)
    (''Car1'', fmap_of_list [
      (''color'', StringValue ''White'')])]"

definition links1 :: "links" where
  "links1 \<equiv> fmap_of_list [
    (''PersonCar'', [''Ivan'',''Car1''])]"

definition data1 :: "data" where
  "data1 \<equiv> (objects1, attr_val1, links1)"

(*
inductive qwe where
  "\<forall>obj. (\<exists>cls vals. fmlookup objects obj = Some cls \<longrightarrow>
   fmlookup attr_vals obj = Some vals \<longrightarrow>
   fmlookup attrs cls = Some cls_attrs) \<Longrightarrow>
   (*fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   type_of_val v = \<tau> \<Longrightarrow>*)
   qwe objects attr_vals attrs"

code_pred [show_modes] qwe .
*)
value attr_val1
value attrs1
value "qwe objects1 attr_val1 attrs1"

term fBall
term fmsubset

value "denorm objects1"

value "denorm3 attrs1"
value "denorm3 attr_val1"
value "(\<lambda>(c,a,v). (the (fmlookup objects1 c), a, type_of_val v)) |`| denorm3 attr_val1"

value "model_is_ok model1"

value "model1 \<turnstile> data1"

definition object_val_ok :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok \<tau> v objects \<equiv> \<forall>cls cls2 obj.
    \<tau> = Class cls \<and>
    v = ObjectValue cls2 obj \<longrightarrow>
    fmlookup objects obj = Some cls"

definition object_val_ok2 :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok2 \<tau> v objects \<equiv>
    case (\<tau>, v)
      of (Class cls, ObjectValue cls2 obj) \<Rightarrow>
            fmlookup objects obj = Some cls
       | (_, _) \<Rightarrow> True"

value "object_val_ok2 (Class ''Person'') (ObjectValue ''Person'' ''Ivan'') objects1"

lemma object_val_ok_eq [code]:
  "object_val_ok \<tau> v objects = object_val_ok2 \<tau> v objects"
  apply (simp only: object_val_ok_def object_val_ok2_def)
  apply (cases \<tau>; simp)
  apply (cases v; simp)
  done

value "object_val_ok (Class ''Person'') (ObjectValue ''Person'' ''Ivan'') objects1"



end
