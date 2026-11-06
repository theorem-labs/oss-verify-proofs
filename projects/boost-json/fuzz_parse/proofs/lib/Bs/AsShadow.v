(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option01Z46Stdlib6ZArith6BinInt1Zm53pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~o3cASHADOW_BASEm53addm53div37Corelib4Init5Logict92eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~v22shm52lem56shiftrm53mult93andm52ltm56modulom53subo38AIMG_TOPv27AAPP_HIv26AHI_LOt92orv2ain_app_memv23nsh69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~hp95hceil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow9Placement~~~~~~htd5aceilv29ALOWSH_LOhtd7aapp_hihtd7aapp_lohtd4aappk14listk14boolk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~imc2b8k13appk14cons37Corelib5Lists7ListDefira6repeatm53eqbm56to_natk16lengthv29shadow_ofm56of_natk14Somek13nat36Stdlib5Lists4Listjh59nth_errort93notv23memo35asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jk95u8arrv24SHADv2cpoison_bytest92exv27byte_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jr13mrdjr12wav2aaccessible3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskg5dov_read_bytesv2baddressablem54landhf9bv_signed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kmeddisjoint_fromkme3ivlkme5munchkme5wmonokme7outsidet93iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ku54cellku52CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lif8rw_cellsv27hull_lov27hull_hikme3stkv25shvis" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition mem : ltac2:(zQ "00S") := ltac2:(zQ "30!h9!jc!l9>0@1$1@1$0#k0@1$2@1$1@1$0#8").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHI_LO  : Z := 0x10007fff8000.
Definition AAPP_HI : ltac2:(zQ "10!m2$0") := ltac2:(zQ "10!nd@2$0+2+if").            (* [comment removed for export] *)
Definition ALOWSH_LO : Z := 0x7fff7000.    (* [comment removed for export] *)

Definition sh : ltac2:(zQ "10!m2>1a$0$0") := ltac2:(zQ "40!m2!re!sd!t3\1a$0@2$2$1@2$3^1+8").

Lemma ASHADOW_BASE_val : ltac2:(zQ "30!ud!m2!re@3$0$1$2+nvvvogg0"). Proof. reflexivity. Qed.

Lemma sh_shiftr : ltac2:(zQ "70!m2!ud!re!hj0!sd!hj5!hja>1a$0>0@2$5Z^1@3$1$0@2$4@2$6^2+3$2@1$3^2").
Proof. intros a Ha. unfold sh. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.

Lemma sh_shiftr' : ltac2:(zQ "70!m2!ud!re!hj0!sd!hj5!hja>1a$0>0@2$5Z^1@3$1$0@2$4$2@2$6^2+3@1$3^2").
Proof. intros a Ha. rewrite <- sh_shiftr by lia. lia. Qed.

Lemma sh_mono : ltac2:(zQ "30!m2!hj0!hj5>1a$0>1b$0>0@2$2^2^1@2$2@1$1^3@1$1^2").
Proof. intros a b H. unfold sh. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.

Lemma sh_add8 : ltac2:(zQ "50!m2!hj0!sd!ud!hk3>1a$0>1k$0@3$3$0@1$1@2$2^2@2$4+8^1@2$2@1$1^2^1").
Proof. intros a k. unfold sh. rewrite Z.add_comm with (n := a). rewrite Z.mul_comm, Z.div_add_l by lia. lia. Qed.

Lemma sh_granule : ltac2:(zQ "80!m2!ud!hj0!hk9!sd!hj5!hkf!hl4>1g$0>1i$0>0@3$1$0@2$7^2+8Z>0@2$3@2$5Z^2@2$6^2+8@3$1$0@1$2@2$4^4^3@1$2^4").
Proof. intros g i Hg Hi. unfold sh. f_equal. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Lemma sh_rel : ltac2:(zQ "80!m2!ud!hj0!sd!t3!hj5!hl4!hld>1A$0>1a$0>0@3$1$0@2$6^2+8Z>0@2$5^3^2@3$1$0@1$2^3@2$3@1$2^4@2$4@2$7^3^4+8").
Proof. intros A a HA Hle. unfold sh. Z.div_mod_to_equations. nia. Qed.

Lemma sh_rel_lt : ltac2:(zQ "90!m2!t3!hk9!sd!hj5!hkf!hld!ud!hl4>1A$0>1a$0>1n$0>0@3$7$0@2$8^3+8Z>0@2$2@2$4^4^3@2$5^3@2$3^4^2@2$2@2$4Z@2$1@2$6^4^5+8@2$5@2$1@2$6^4^5+8@2$1@2$3^3+7+8").
Proof. intros A a n HA H. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)

Lemma sh_above_image : ltac2:(zQ "40!hj5!m2!hm3!hj0>1a$1>0@2$0Z^1@2$0$2@1$3^2").
Proof. intros a H. unfold sh, AIMG_TOP, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.

Lemma sh_below_app : ltac2:(zQ "70!hkf!hk9!m2!hme!hn8!hj0!hj5>1a$2>0@2$1@2$6Z^1@2$0^1$3@2$0@1$5^2$4").
Proof. intros a H. unfold sh, AHI_LO, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_app_mem : ltac2:(zQ "10!m2>2lo$0>2hi$0P") := ltac2:(zQ "80!hj5!hk9!m2!sd!ho1!re!hme!hn8\2lo$2\2hi$2@2$4@2$1@2$0Z^2@2$0@2$3^1+8$5@2$1@2$0$7^2@2$0@2$3^1+8$6").

Lemma in_app_mem_sub : ltac2:(zQ "30!m2!ho6!hj5>2lo$0>2hi$0>3lo'$0>3hi'$0>0@2$1^4^3>0@2$2^5^3>0@2$2^3^5@2$1^5^4").
Proof. intros lo hi lo' hi' H ? ?. unfold in_app_mem in *. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nsh : ltac2:(zQ "10!m2>1n$0$0") := ltac2:(zQ "30!m2!sd!t3\1n$0@2$2@2$1^1+7+8").

(* [comment removed for export] *)
Lemma sh_nsh_high : ltac2:(zQ "70!hj5!m2!sd!hme!hn8!hp3!hj0>1A$1>1n$1>0@2$0Z^2>0@2$0Z^2>0@2$0@2$2^4^3$3@2$0@2$2@1$6^5@1$5^4$4").
Proof. intros A n HA Hn Htop. unfold sh, nsh, AHI_LO, AAPP_HI, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Placement.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition aceil : ltac2:(zQ "10!m2$0") := ltac2:(zQ "30!ht4!hl4!hld@2$2@1$0?5HCEIL@2$1@1$0?5HCEIL+hgg0").

  Lemma aceil_facts : ltac2:(zQ "90!ii5!hk9!hj5!ht4!ud!m2!sd!hkf!hl4@2$1@2$1@2$2+nvvvnvogggg0$0@2$2$0+nvvvvvogggg0@2$1@3$4$5@2$8$0+hgg0Z@2$1@2$2$0@1$3?5HCEIL@2$7@1$3?5HCEIL@2$6$0+hgg0").
  Proof. hcb. unfold aceil. Z.div_mod_to_equations. lia. Qed.
  Lemma aceil_range : ltac2:(zQ "30!ii5!hj5!hk9@2$2@2$1+nvvvnvogggg0$0@2$1$0+nvvvvvogggg0").  Proof. pose proof aceil_facts. lia. Qed.
  (* [comment removed for export] *)
  Lemma grant_below_aceil : ltac2:(zQ "70!m2!ud!sd!hj5!hl4!ii5!ht4>1a$0>3len$0>0@3$1$0@2$4^2+hgg0Z>0@3$1$0@2$4^2+hgg0Z>0@2$3@2$2^4^3@1$6?5HCEIL@2$3@2$2^5^4$5").
  Proof. intros a len Ha Hl H. unfold aceil. Z.div_mod_to_equations. lia. Qed.

  Definition aapp_lo : ltac2:(zQ "10!m2>1A$0>1n$0P") := ltac2:(zQ "60!m2!hj5!hk9!hm3!iie!sd\1A$0\1n$0@2$2@2$1$3^2@2$1@2$5^2^1$4").
  Definition aapp_hi : ltac2:(zQ "10!m2>1A$0>1n$0P") := ltac2:(zQ "60!m2!hj5!hk9!hn8!ii5!sd\1A$0\1n$0@2$2@2$1$3^2@2$1@2$5^2^1$4").
  Definition aapp : ltac2:(zQ "10!m2>1A$0>1n$0P") := ltac2:(zQ "40!m2!ho1!ija!ik5\1A$0\1n$0@2$1@2$3^2^1@2$2^2^1").


  Lemma aapp_sub : ltac2:(zQ "40!m2!il0!sd!hj5>1A$0>1n$0>2A'$0>2n'$0>0@2$1^4^3>0@2$3^5^3>0@2$3@2$2^4^3@2$2^6^5@2$1^5^4").
  Proof. intros A n A' n' H ? ?. unfold aapp, aapp_lo, aapp_hi in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma aapp_bounds : ltac2:(zQ "a0!hk9!hj5!m2!ii5!sd!hkf!hm3!hme!il0!ht4>1A$2>1n$2>0@2$8^2^1>0@2$1Z^2@2$0@2$1$6^4@2$0@2$1@2$4^4^3$3@2$0@2$5@2$4^4^3$7@2$0@2$5Z^4@2$1$3@1$9?5HCEIL").
  Proof. intros A n H Hn. pose proof aceil_facts. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma aapp_in_app_mem : ltac2:(zQ "50!m2!hj5!il0!ho6!sd>1A$0>1n$0>2lo$0>2hi$0>0@2$2^4^3>0@2$1^5^3>0@2$1^3@2$4^6^5@2$3^5^4").
  Proof. intros A n lo hi H ? ?. pose proof aceil_facts. unfold aapp, aapp_lo, aapp_hi, in_app_mem, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma aapp_not_shadowland : ltac2:(zQ "70!m2!hj5!ho1!hn8!iie!il0!sd>1A$0>1n$0>0@2$5^2^1@2$2@2$1@2$6^3^2$4@2$1$3^3").
  Proof. intros A n H. unfold aapp, aapp_lo, aapp_hi in H. lia. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma aapp_disjoint_sh : ltac2:(zQ "80!hj5!m2!sd!hj0!ho1!hme!il0!hp3>1B$1>1k$1>1a$1>1j$1>0@2$6^4^3>0@2$0Z^3>0@2$0@2$2^4^3$5>0@2$0Z^4@2$4@2$0@2$2@1$3^6@1$7^5^8@2$0@2$2^8^7@1$3^6").
  Proof.
    intros B k a j HB Ha Hj Hj0. pose proof aceil_facts. unfold nsh.
    unfold aapp, aapp_lo, aapp_hi, sh, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.
    Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_below_aceil : ltac2:(zQ "70!hkf!hk9!m2!hme!ii5!hj0!hj5>1a$2>0@2$1@2$6Z^1@2$0^1$3@2$0@1$5^2$4").
  Proof. intros a H. pose proof aceil_facts. unfold sh, AAPP_HI, ASHADOW_BASE in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma aapp_above_image : ltac2:(zQ "40!m2!hm3!il0!hj5>1A$0>1n$0>0@2$2^2^1@2$3$1^3").
  Proof. intros A n H. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in *. lia. Qed.
  Lemma sh_aapp_range : ltac2:(zQ "b0!hj0!hj5!hk9!m2!ii5!hm3!hn8!il0!hp3!sd!hkf>1A$3>1n$3>0@2$7^2^1>0@2$1Z^2@2$2@2$1@1$0$5@1$0^4@2$2@2$1@2$9@1$0^4@1$8^3@1$0$4@2$a@1$0$4$6").
  Proof.
    intros A n H Hn. pose proof aceil_facts. unfold nsh.
    unfold aapp, aapp_lo, aapp_hi, sh, AIMG_TOP, ALOWSH_LO, AHI_LO, ASHADOW_BASE in *.
    Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma sh_aapp_lo_range : ltac2:(zQ "70!hj5!m2!hj0!hk9!ik5!hp3!sd>1A$1>1n$1>0@2$4^2^1>0@2$0Z^2@2$3@2$0+oggtqmg0@1$2^4@2$0@2$6@1$2^4@1$5^3+ovvvmug0").
  Proof. intros A n H Hn. unfold nsh, aapp_lo, sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_aapp_hi_range : ltac2:(zQ "a0!hj0!hj5!hk9!m2!ii5!hn8!ija!hp3!sd!hkf>1A$3>1n$3>0@2$6^2^1>0@2$1Z^2@2$2@2$1+iggovvvngg0@1$0^4@2$2@2$1@2$8@1$0^4@1$7^3@1$0$4@2$9@1$0$4$5").
  Proof. intros A n H Hn. pose proof aceil_facts. unfold nsh, aapp_hi, sh, AHI_LO, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
End Placement.

(* [comment removed for export] *)
Ltac acb :=
  let K := fresh "ACEILB" in
  pose proof (aceil_facts : 0x7fff7f800000 <= aceil <= 0x7fffff800000 /\ aceil mod 4096 = 0 /\ aceil <= hceil < aceil + 4096) as K.
Ltac aapp_unfold :=
  try acb; unfold aapp, aapp_lo, aapp_hi, in_app_mem, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO, AAPP_HI, ASHADOW_BASE in *.

(* [comment removed for export] *)
Definition shadow_of : ltac2:(zQ "40!il8!h9!m2!jc>1n$2@1$0@1$3@1$1#8") := ltac2:(zQ "e0!h9!jc!ilf!im6!iq7!hl4!iqd!ir3!il8!it1!m2!t3!itb!iu1\1n$a@3$6@1$1@1$0#8@3$9@1$1@1$0#8@1$4Z@1$d@2$b^1+8M2\0$2@1$8@1$1@1$0#8@2$c@2$5^1+8Z@1$3@1$1@1$0#8@3$7@1$1@1$0#8@1$4@2$5^1+8@1$3@1$1@1$0#8").

Lemma shadow_of_length : ltac2:(zQ "90!m2!iua!ud!h9!hp3!iv3!hj5!ivf!jc>1n$0>0@2$6Z^1@3$2$0@1$7@2$1@1$8@1$3#8@1$5^2@1$4^2").
Proof.
  intros n Hn. unfold shadow_of, nsh. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_of_mult8 : ltac2:(zQ "c0!ud!h9!m2!jc!il8!it1!iv3!iq7!t3!hj5!hl4!iu1>1n$2>0@2$9Z^1>0@3$0$2@2$a^2+8Z@3$0@1$4@1$3@1$1#8@1$6^3@3$5@1$3@1$1#8@1$7Z@1$b@2$8^3+8").
Proof. intros n Hn E. unfold shadow_of. rewrite E. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma shadow_of_nth_full : ltac2:(zQ "e0!h9!jc!jg8!jgf!l9!ud!m2!iv3!iq7!ji8!t3!hj5!hkf!ivf>1n$6>1i$3>0@2$bZ^2>0@2$c@1$d^2@2$a^3+8@3$5@1$4@1$1@1$0#8@3$9@1$1@1$0#8@1$7^4^3@2$2@1$1@1$0#8@1$8Z").
Proof.
  intros n i Hn Hi. unfold shadow_of. rewrite nth_error_app1 by (rewrite repeat_length; lia).
  apply nth_error_repeat. lia.
Qed.

Lemma shadow_of_nth_last : ltac2:(zQ "e0!h9!jc!ud!m2!hl4!jg8!l9!jj5!iv3!iq7!ji8!t3!hj5!iu1>1n$3>0@2$cZ^1>0@1$7@3$2$3@2$4^2+8Z@3$2@1$6@1$1@1$0#8@3$a@1$1@1$0#8@1$8^3@1$d@2$b^3+8@2$5@1$1@1$0#8@1$9@2$4^3+8").
Proof.
  intros n Hn E. unfold shadow_of. rewrite nth_error_app2 by (rewrite repeat_length; lia).
  rewrite repeat_length, Nat.sub_diag. destruct (Z.eqb_spec (n mod 8) 0); [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Definition poison_bytes : ltac2:(zQ "50!il8!jgf!h9!m2!jc>1k$1>1v$3@1$0@1$4@1$2#8") := ltac2:(zQ "60!jgf!it1!h9!m2!iq7!jc\1k$0\1v$3@3$1@1$5@1$2#8@1$4^1^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SHAD : ltac2:(zQ "50!il8!h9!m2!jjb!jc>1m$3>1A$2>3sbs@1$0@1$4@1$1#8P") := ltac2:(zQ "c0!hk9!m2!il8!ud!h9!jk1!jjb!hj0!jo3!hj5!hl4!jc\1m$6\1A$1\3sbs@1$2@1$b@1$4#8@2$0@2$9Z^2@2$0@3$3$1@2$a^2+8Z@4$8$5^3@1$7^2^1").

Definition addressable : ltac2:(zQ "20!m2!jjb>1m$1>1A$0>1n$0P") := ltac2:(zQ "60!m2!hk9!joc!jjb!iv3!hj5\1m$3\1A$0\1n$0@2$1@2$5Z^1@3$2^3^2@1$4^1").

Definition poisoned : ltac2:(zQ "30!m2!jgf!jjb>1m$2>1A$0>1k$1>1v$0P") := ltac2:(zQ "50!m2!jgf!joc!jjb!jp3\1m$3\1A$0\1k$1\1v$0@3$2^4^3@2$4^2^1").

(* [comment removed for export] *)
Definition byte_ok : ltac2:(zQ "10!m2>1v$0>1x$0P") := ltac2:(zQ "60!m2!ud!ho1!sd!hj5!hl4\1v$0\1x$0@2$2@3$1$0^2Z@2$4@2$3@2$5^1+8+1^2").
Definition accessible : ltac2:(zQ "20!m2!jjb>1m$1>1a$0>1n$0P") := ltac2:(zQ "h30!hk9!m2!hj5!h9!sd!hkf!jc!jg8!l9!ud!jq2!jk1!hme!jq7!jjb!hj0!jub!jv2!iq7\1m$e\1a$1\1n$1@2$0@2$2Z^2@2$0@2$2@2$4^2^1$c>1x$1>0@2$0@2$2^3^1@2$5^1@2$4^3^2@2$a$1\1v$1@2$0@2$0@2$2Z^1@2$5^1+8@2$0@3$9@1$8@1$6@1$3#8@3$h0$b^6@1$h1@1$f^3@2$7@1$6@1$3#8@1$h2^1@2$d^1^3").

Lemma accessible_nil : ltac2:(zQ "60!hj5!hk9!m2!hme!jv8!jjb>1m$5>1a$2>0@2$1@2$0Z^1@2$0^1$3@3$4^3^2Z").
Proof. intros m a H. split; [lia|]. split; [lia|]. intros x Hx. lia. Qed.

Lemma accessible_sub : ltac2:(zQ "50!m2!hj5!jv8!sd!jjb>1m$4>1a$0>1n$0>2a'$0>2n'$0>0@3$2^5^4^3>0@2$1^5^3>0@2$1@2$3^4^3@2$3^6^5>0@2$1Z^4@3$2^9^6^5").
Proof.
  intros m a n a' n' (H0 & H1 & H) ? ? ?. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma SHAD_read : ltac2:(zQ "h30!h9!jc!il8!ud!jg8!l9!m2!ir3!im6!kjc!jk1!joc!jjb!hj0!jv2!ji8!sd!hj5!iu1>1m$c>1A$6>3sbs@1$2@1$1@1$0#8>1i$6>1b@1$1@1$0#8>1x@1$1@1$0#k0>0@3$b^6^5^4>0@3$3@1$5@1$1@1$0#8@3$f@1$1@1$0#8^5@1$h2^4@2$4@1$1@1$0#8^3>0@2$h1Z^5>0@3$3@1$1@1$0#k0^4@1$e@2$h0@1$d^8^6@3$3@1$5@1$2@1$1@1$0#8@4$9$a^a^5N1@2$4@1$2@1$1@1$0#8@3$7@1$1@1$0#8^6@1$8@1$1@1$0#8").
Proof. (intros m A sbs i b x nd_i2 Hn Hi ->; ndestruct nd_i2 as (_ & _ & U)). eapply u8arr_read; eauto. Qed.

(* [comment removed for export] *)
Lemma SHAD_read_at : ltac2:(zQ "h40!h9!jc!il8!ud!jg8!l9!m2!ir3!im6!kjc!jk1!joc!jjb!hj0!jv2!ji8!t3!hj5!hld!iu1>1m$c>1A$6>3sbs@1$2@1$1@1$0#8>1a$6>1b@1$1@1$0#8>1x@1$1@1$0#k0>0@3$b^6^5^4>0@2$h1^6^4>0@3$3@1$5@1$1@1$0#8@3$f@1$1@1$0#8^6@1$h3@2$h0@2$h2^5^7+8@2$4@1$1@1$0#8^4>0@3$3@1$1@1$0#k0^4@1$e@1$d^6@3$3@1$5@1$2@1$1@1$0#8@4$9$a^a^5N1@2$4@1$2@1$1@1$0#8@3$7@1$1@1$0#8^6@1$8@1$1@1$0#8").
Proof.
  intros m A sbs a b x SH Hle Hn ->. npose SH as (_ & HA & _).
  rewrite (sh_rel A a HA Hle). eapply SHAD_read; eauto. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma SHAD_mrd_at : ltac2:(zQ "h20!h9!jc!jg8!l9!ud!m2!il8!jk1!joc!jjb!hj0!jub!jv2!ji8!t3!hj5!hld!iu1>1m$9>1A$5>3sbs@1$6@1$1@1$0#8>1a$5>1b@1$1@1$0#8>0@3$8^5^4^3>0@2$f^5^3>0@3$4@1$3@1$1@1$0#8@3$d@1$1@1$0#8^5@1$h1@2$e@2$h0^4^6+8@2$2@1$1@1$0#8^3@3$4@1$3@1$1@1$0#8@3$b$7^8@1$c@1$a^5@2$2@1$1@1$0#8^4").
Proof.
  intros m A sbs a b SH Hle Hn. npose SH as (A0 & HA & [(B0 & B1 & HB) _]).
  pose proof (nth_error_lt _ _ _ Hn) as L.
  rewrite (sh_rel A a HA Hle). rewrite <- Hn.
  replace ((a - A) / 8) with (Z.of_nat (Z.to_nat ((a - A) / 8))) at 1 by (Z.div_mod_to_equations; nia).
  apply HB. exact L.
Qed.

(* [comment removed for export] *)
Lemma addressable_read0 : ltac2:(zQ "h50!h9!jc!m2!il8!ud!hj5!jg8!ir3!im6!l9!kjc!jk1!kkd!jjb!hj0!jv2!iq7!sd!t3!hk3!hld>1m$d>1A$2>1n$2>1a$2>1x@1$1@1$0#k0>0@3$c^5^4^3>0@2$5^5^3>0@2$5@2$h1@2$h3+8@2$h2@2$h4^4^6+8+8^5>0@3$4@1$1@1$0#k0^4@1$f@1$e^5@3$4@1$9@1$3@1$1@1$0#8@4$a$b^9^5N1@2$6@1$3@1$1@1$0#8@3$7@1$1@1$0#8@1$h0Z@1$8@1$1@1$0#8").
Proof.
  intros m A n a x [Hn SH] Hle Hfull ->. npose SH as (_ & HA & _).
  eapply SHAD_read_at; eauto. apply shadow_of_nth_full; [lia|]. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma addressable_read0_w : ltac2:(zQ "h40!h9!jc!m2!hj5!il8!ud!sd!jg8!ir3!im6!l9!kjc!jk1!kkd!jjb!hj0!jv2!iq7!t3!hk3>1m$e>1A$2>1n$2>1a$2>1w$2>1x@1$1@1$0#k0>0@3$d^6^5^4>0@2$3^6^4>0@2$3+1^4>0@2$3@2$6^6^5@2$6^8@2$h3+8@2$h2^7+8>0@3$5@1$1@1$0#k0^5@1$h0@1$f^7@3$5@1$a@1$4@1$1@1$0#8@4$b$c^b^6N1@2$7@1$4@1$1@1$0#8@3$8@1$1@1$0#8@1$h1Z@1$9@1$1@1$0#8").
Proof.
  intros m A n a w x AD Hle Hw Hhi ->. pose proof AD as [Hn (_ & HA & _)].
  eapply addressable_read0; eauto. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma land7_mod8 : ltac2:(zQ "50!m2!ud!klb!hj5!hl4>1a$0>0@2$3Z^1@3$1$0@2$2^2+7@2$4^2+8").
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)

Lemma b8_signed_small : ltac2:(zQ "80!m2!hk9!ud!h9!iq7!hj5!hkf!km2>1v$0>0@2$1@2$5Z^1@2$6^1+o0@3$2$0@2$7@1$3#8@1$4^2^2").
Proof.
  intros v Hv. unfold b8. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [N.sub Z.of_N Z.pow_pos Pos.iter Z.mul].
  change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma addressable_accessible : ltac2:(zQ "70!m2!sd!hj5!hme!jv8!kkd!jjb>1m$6>1A$0>1n$0>1a$0>1k$0>0@3$5^5^4^3>0@2$2^5^3>0@2$2@2$1^4^3@2$1^6^5>0@2$2@2$1^7^6$3@3$4^9^6^5").
Proof.
  intros m A n a k AD Hle Hhi Htop. pose proof AD as [Hn (A0 & HA & U)].
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z.lt_ge_cases x (A + 8 * (n / 8))) as [FULL|PART].
  - exists 0. split; [lia|]. split; [| left; reflexivity].
    eapply SHAD_mrd_at; [split; [exact A0| split; [exact HA| exact U]] | lia |].
    apply shadow_of_nth_full; [lia|]. Z.div_mod_to_equations. nia.
  - assert (Hm : n mod 8 <> 0) by (Z.div_mod_to_equations; nia).
    exists (n mod 8). split; [Z.div_mod_to_equations; lia|]. split.
    + eapply SHAD_mrd_at; [split; [exact A0| split; [exact HA| exact U]] | lia |].
      replace ((x - A) / 8) with (n / 8) by (Z.div_mod_to_equations; nia).
      apply shadow_of_nth_last; lia.
    + right. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma SHAD_aligned : ltac2:(zQ "a0!m2!il8!hk9!ud!h9!joc!jjb!hj5!hl4!jc>1m$6>1A$0>3sbs@1$1@1$9@1$4#8>0@3$5^3^2^1@2$2@2$7Z^3@3$3$0@2$8^3+8Z"). Proof. (intros m A sbs nd_i3; ndestruct nd_i3 as (H0 & H & _)). auto. Qed.

(* [comment removed for export] *)

Lemma SHAD_transport : ltac2:(zQ "f0!h9!jc!il8!joc!iua!l9!m2!jk1!jjb!hj0!kqa!krb!ks2!ksb!ivf>1W@1$2$b>1m$8>2m'>0@1$1@1$0#k0@1$5@1$1@1$0#8>1A$6>3sbs@1$2@1$1@1$0#8>0@3$3^4^2^1>0@3$c^6^5^4>0@3$d$7^6^5>0@3$a^8@1$9^5@1$e@2$4@1$1@1$0#8^4@3$3^7^6^5").
Proof. (intros W m m' A sbs nd_i4 MU WM D; ndestruct nd_i4 as (A0 & HA & U)). split; [exact A0|]. split; [exact HA| eapply u8arr_transport; eauto]. Qed.

Lemma addressable_transport : ltac2:(zQ "e0!h9!m2!kkd!jc!il8!l9!jk1!jjb!hp3!hj0!kqa!krb!ks2!ksb>1W@1$4$b>1m$7>2m'>0@1$3@1$0#k0@1$5@1$3@1$0#8>1A$1>1n$1>0@3$2^4^2^1>0@3$c^6^5^4>0@3$d$6^6^5>0@3$a^8@1$9^5@1$8^4@3$2^7^6^5").
Proof.
  intros W m m' A n [Hn SH] MU WM D. split; [exact Hn|]. eapply SHAD_transport; eauto.
  rewrite shadow_of_length by lia. exact D.
Qed.

(* [comment removed for export] *)
Lemma accessible_transport : ltac2:(zQ "f0!m2!h9!jv8!jc!il8!l9!hk9!jjb!hj0!krb!ks2!kt4!sd!hj5!hkf>1W@1$4$9>1m$7>2m'>0@1$3@1$1#k0@1$5@1$3@1$1#8>1a$0>1n$0>0@3$2^4^2^1>0@3$a^6^5^4>0>1x$0>0@2$6@2$d^5^1@2$e^1@2$c^5^4@2$b^9@1$8^2@3$2^6^5^4").
Proof.
  (intros W m m' a n nd_i5 MU OUT; ndestruct nd_i5 as (A0 & A1 & AC)). split; [exact A0|]. split; [exact A1|].
  intros x Hx. ndestruct (AC x Hx) as (v & V0 & RD & OK). exists v. split; [exact V0|]. split; [| exact OK].
  unfold mrd in *. unfold wa in *. rewrite MU; [exact RD|].
  rewrite unsigned_lit; [apply OUT; exact Hx|]. unfold sh, AAPP_HI, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma accessible_read1 : ltac2:(zQ "h70!h9!m2!jc!hk9!il8!ud!hj5!jg8!ir3!im6!l9!jq2!ho1!kjc!jk1!jv8!jjb!hj0!jv2!iq7!sd!hkf!hl4>1m$h0>1a$1>0@3$f^2^1+1@2$b$1\1v$1@2$3@2$3@2$6Z^1@2$h5^1+8@2$3@2$c@3$5$1^1Z@2$6@2$h4@2$h6^3+8+1^1@3$5@1$a@1$4@1$2@1$0#8@4$d$e^4@1$h2@1$h1^3N1@2$7@1$4@1$2@1$0#8@3$8@1$2@1$0#8@1$h3^1@1$9@1$2@1$0#8").
Proof.
  (intros m a nd_i6; ndestruct nd_i6 as (A0 & A1 & AC)). ndestruct (AC a ltac:(lia)) as (v & V0 & RD & OK). exists v. split; [exact V0|]. split; [exact OK|].
  rewrite ov_rdn. cbn [rdn]. unfold mrd in RD.
  destruct (m (wa (sh a))) as [b|] eqn:E.
  - inversion RD; subst. reflexivity.
  - destruct (seg_rom asegs (wa (sh a))) as [b|]; [| discriminate RD]. inversion RD; subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma SHAD_app : ltac2:(zQ "d0!h9!jc!joc!il8!iqd!iua!hk9!ktf!m2!jjb!sd!hk3!ivf>1m$9>1A$8>2s1@1$3@1$1@1$0#8>2s2@1$3@1$1@1$0#8@2$7@3$2^4^3@3$4@1$1@1$0#8^2^1@2$6@3$2^4^3^2@3$2^4@2$a^3@2$b+8@1$c@2$5@1$1@1$0#8^2^1").
Proof.
  intros m A s1 s2. unfold SHAD, u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite sh_add8.
  split.
  - (intros nd_i7; ndestruct nd_i7 as (A0 & HA & (B1 & B2) & (W1 & W2))). split; [split; [exact A0| split; [exact HA| split; assumption]]|].
    split; [lia|]. split; [Z.div_mod_to_equations; nia|]. split; assumption.
  - intros ((A0 & HA & B1 & W1) & (_ & _ & B2 & W2)). split; [exact A0|]. split; [exact HA|]. split; split; assumption.
Qed.

(* [comment removed for export] *)
Lemma addressable_split8 : ltac2:(zQ "90!m2!kkd!hk9!ud!hj5!hl4!jjb!sd!hld>1m$6>1A$0>1n$0>1k$0>0@3$1^4^3^2>0@3$3$0@2$5^3+8Z>0@3$3$0@2$5^3+8Z>0@2$2@2$4Z^4@2$4^4^5@2$2@3$1^8^7^5@3$1^8@2$7^7^5@2$8^6^5").
Proof.
  intros m A n k [Hn SH] En Ek Hk.
  rewrite shadow_of_mult8 in SH by lia.
  replace (Z.to_nat (n / 8)) with (Z.to_nat (k / 8) + Z.to_nat ((n - k) / 8))%nat in SH by (Z.div_mod_to_equations; nia).
  rewrite repeat_app in SH. apply SHAD_app in SH. destruct SH as [S1 S2].
  rewrite repeat_length in S2. replace (8 * Z.of_nat (Z.to_nat (k / 8))) with k in S2 by (Z.div_mod_to_equations; nia).
  split; (split; [lia|]); rewrite shadow_of_mult8 by (try lia; Z.div_mod_to_equations; nia); assumption.
Qed.

(* [comment removed for export] *)
Lemma SHAD_rw_cells : ltac2:(zQ "e0!h9!li1!jc!ir3!iua!il8!im6!m2!jk1!joc!jjb!hj0!li9!lma>1m$a>1A$7>3sbs@1$5@1$2@1$0#8>0@3$9^3^2^1@4$d$8^4@1$b^3@3$3$1@2$c@2$4@1$2@1$0#8^2^2@1$6$1").
Proof. (intros m A sbs nd_i8; ndestruct nd_i8 as (_ & _ & U)). apply rw_cells_of_u8arr. exact U. Qed.

Lemma SHAD_of_rw_cells : ltac2:(zQ "h10!h9!jc!m2!li1!ir3!il8!jgf!im6!l9!ud!jk1!joc!hj0!li9!lma!hj5!hl4>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$2>1n$6>3sbs@1$5@1$1@1$0#8>0@2$fZ^3>0@3$9$2@2$h0^4+8Z>0@4$e$a^6@1$c^5@3$4$3@2$d^4^3@1$7$3@3$b^7^6^4").
Proof. intros m A n sbs A0 HA RC. split; [exact A0|]. split; [exact HA| eapply u8arr_of_rw_cells; exact RC]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hull_lo : ltac2:(zQ "10!m2>1a$0$0") := ltac2:(zQ "30!m2!hl4!hld\1a$0@2$2^1@2$1^1+k0").
Definition hull_hi : ltac2:(zQ "10!m2>1b$0$0") := ltac2:(zQ "40!hl4!m2!sd!hld\1b$1@2$2^1@2$0@2$3+k0@2$0^1+k0+k0").

Lemma hull_lo_le : ltac2:(zQ "80!ln6!hk9!m2!hj5!ud!sd!hkf!hl4>1a$2>0@2$3Z^1@2$1@2$3@1$0^2^2@2$1@2$6^2@2$5@1$0^2+k0@3$4$2@2$7@1$0^2+k0Z").
Proof. intros a Ha. unfold hull_lo. Z.div_mod_to_equations. nia. Qed.
Lemma hull_hi_ge : ltac2:(zQ "80!lo0!hk9!m2!hj5!ud!sd!hkf!hl4>1b$2>0@2$3Z^1@2$1@2$3^2@1$0^2@2$1@2$6@1$0^2@2$5^2+k0@3$4$2@2$7@1$0^2+k0Z").
Proof. intros b Hb. unfold hull_hi. Z.div_mod_to_equations. nia. Qed.

Definition shvis : ltac2:(zQ "20!m2!jjb>1m$1>2lo$0>2hi$0P") := ltac2:(zQ "70!m2!hj0!jk1!lo0!ln6!jjb!loa\1m$5\2lo$0\2hi$0@4$6$2^3@1$1@1$4^2@1$1@1$3^1").

Lemma shvis_sub : ltac2:(zQ "40!hj5!m2!lp1!jjb>1m$3>2lo$1>2hi$1>3lo'$1>3hi'$1>0@3$2^5^4^3>0@2$0Z^5>0@2$0^6^4>0@2$0^4^6>0@2$0^6^5>0@2$0Z^8@3$2^b^8^7").
Proof.
  intros m lo hi lo' hi' SV ? ? ? ? ?. unfold shvis in *.
  pose proof (hull_lo_le lo) as HL. pose proof (hull_lo_le lo') as HL'. pose proof (hull_hi_ge hi) as HH. pose proof (hull_hi_ge hi') as HH'.
  assert (L1 : sh (hull_lo lo) <= sh (hull_lo lo')). { apply sh_mono. unfold hull_lo in *. Z.div_mod_to_equations. nia. }
  assert (L2 : sh (hull_hi hi') <= sh (hull_hi hi)). { apply sh_mono. unfold hull_hi in *. Z.div_mod_to_equations. nia. }
  ndestruct SV as (S0 & S1 & SS). split; [lia|]. split; [lia|]. intros a Ha. apply SS. lia.
Qed.

Lemma shvis_transport : ltac2:(zQ "h00!hj0!h9!m2!ln6!lp1!jc!il8!l9!jk1!lo0!jjb!kqa!krb!ks2!ksb!hld>1W@1$6$c>1m$a>2m'>0@1$5@1$1#k0@1$7@1$5@1$1#8>2lo$2>2hi$2>0@3$4^4^2^1>0@3$d^6^5^4>0@3$e$8^6^5>0@3$b^8@1$0@1$3^5@2$f@1$0@1$9^4@1$0@1$3^5@3$4^7^6^5").
Proof. intros. unfold shvis in *. eapply stk_transport_disjoint; eauto. Qed.
(* [comment removed for export] *)
