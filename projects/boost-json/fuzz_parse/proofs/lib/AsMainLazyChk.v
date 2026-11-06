(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanInit
  AsImages AsPlanImages AsHSTab AsStartupHSF AsStartupCerts AsMainVM AsMainState AsMainFacts LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsMainSyms.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~03lin37Corelib4Init9Datatypesk64prod69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsMainVM~~~~~~m53sivk63fstk64pairk63sndm54lcat37Corelib7Numbers7BinNumss01Z03env79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~u24lden46Stdlib6ZArith6BinInt1Zhj03subk64listk64bool79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~hld4bctx36Stdlib5Lists4Listhq87forallbm5ddisjoint_decBhj02lek64true37Corelib4Init5Logichu32eqhu32orhld4mkbc37Corelib5Lists7ListDefigb3map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsMainSyms~~~~~~ii9epairwise_apart69OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsMainLazyChk~~~~~~inbfall_pairs_disjBinb4sivZhq82Ininbbcross_disjB04exprk64cons04EVark63nilk64andbm56lconstm57le_linB79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsMainLazyChk4FPX2~~~~~~jhe5HULLSjhe4SHHSjhe4STKShj03powhu33andinb4STKSigb6Forallinb7placedBk63natk63app69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainFacts~~~~~~jr35K_B04jr35K_B05jr35K_B06jr35K_B08jr35K_B09jr35K_B10jr35K_B11jr35K_B12jr35K_B16jr35K_B20jr35K_B21jr35K_B22jr35K_B23jr35K_B24jr35K_B25jr36K_METAjr32pgjr33pgo79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsMainLazyChk4FPX3~~~~~~kof4KPSkkof4ksivhj02ltjr32vEhj03mulhj03addkof3KPSjr36DG_visigb6firstnigb5skipnjr35K_B13inb4asivjr37DG_lazyhq82tlhldclin_nowrapRB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ll43acsll47a_ghostll42kn04ELit3h5LinuxProcessSemantics5Riscv5Instrlr05M_MULjr38has_factkof4APPSkof4KPSXkof3LZSkof7vis_nwBm58kn_arithll45a_visll48list_eqbll48pair_eqb03EMd06KRangehq87existsbhj03eqbkof4zmemkof3evzhq88flat_mapkof6zinterlr05aluoplr05mulopkof8lin_hasZk63orbhj06of_nat46Stdlib5Arith8PeanoNat3Natmq93eqb0cmentions_var0ashares_varkof6lin_vzm57lin_haskofakdisj_preZm59kdisj_prekof3kdp06kentryk66option05saddr06a_basem58lin_ofaBm58lin_ofxBkof7kdprep1hld5bc_fkkof4sivzkof7kdisjP1kofddisjoint_decPkof4mkszinb5HULLSinb4SHHSm57kdisj1Bkof6kdprepkoffall_pairs_disjPkofbcross_disjPkof7placedPkof8lz_checkkof9lz_checkPk64Somejr3ahole_classjr3chole_granted69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~oi08HSF_asans04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~on22uE06lin_of35stdpp9bitvectorbdefinitionsos42bv3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeou77Segmentu27know_ok" s.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition asiv : ltac2:(zQ "30!k1!le!q0>1p@2$1$0$0$2") := ltac2:(zQ "60!k1!q6!qc!le!r3!r9\1p@2$3$0$0@4$2$0$0@3$1$0$0^1@2$5@3$1$0$0^1@3$4$0$0^1").
Definition sivZ : ltac2:(zQ "40!t9!le!q0!td>1E$3>1s$2@2$1$0$0") := ltac2:(zQ "90!k1!hi9!q6!t9!qc!r3!q0!td!hk8\1E$7\1s$6@4$4$3$3@2$1^2@3$2$0$0^1@2$8@2$1^2@3$5$0$0^1@2$1^2@3$2$0$0^1").   (* [comment removed for export] *)

Fixpoint all_pairs_disjB (bc : bctx) (l : list siv) : bool :=
  match l with [] => true | x :: r => forallb (fun y => disjoint_decB bc x y) r && all_pairs_disjB bc r end.
Definition cross_disjB : ltac2:(zQ "40!hkf!q0!hl6!hq0>2bc$3>2l1@1$0$1>2l2@1$0$1$2") := ltac2:(zQ "50!q0!hkf!hrb!hs6!hq0\2bc$4\2l1@1$1$0\2l2@1$1$0@3$2$0\1x$0@3$2$0\1y$0@3$3^5^2^1^2^2").
End FPX1.

Section CheckSound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!hkf!phc@1$0$1").
  Variable E : ltac2:(zQ "10!td$0").
  Variable M : ltac2:(zQ "30!omb!ou1!ni2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable fk : ltac2:(zQ "20!hkf!nha@1$0$1").
  Hypothesis KN : ltac2:(zQ "10!pi7@4$0?4segs?1E?1M?2fk").
  #[local] Notation bc := (mkbc fk).

  Lemma disjoint_decB_soundZ : ltac2:(zQ "c0!k1!hi9!q6!r3!q0!ht6!hl6!htc!hv7!hvd!hs6!ig3>1x$4>1y$4>0@3$8$6@3$a@1$b?2fk^2^1$7@2$9@2$5@2$1?1E@3$3$0$0^3@2$1?1E@3$2$0$0^2@2$5@2$1?1E@3$3$0$0^2@2$1?1E@3$2$0$0^3").
  Proof. intros x y H. rewrite disjoint_decB_eqf in H. exact (disjoint_dec_sound segs E M fk KN x y H). Qed.

  Lemma all_pairs_disjB_sound : ltac2:(zQ "c0!t9!q0!hl6!hkf!le!htc!hv7!ii2!im9!irb!ise!ig3>1l@1$3$1>0@3$6$2@2$9@1$b?2fk^1$5@1$8@4$7$1@2$4$0$0@1$a?1E^2").
  Proof.
    induction l as [|x l IH]; intros H; cbn [all_pairs_disjB map pairwise_apart]; [exact I|].
    apply andb_prop in H as [H1 H2]. unfold sivZ at 1. cbn [fst snd]. split; [|exact (IH H2)].
    apply Forall_map. apply Forall_forall. intros y Hy. cbn [fst snd].
    pose proof (proj1 (forallb_forall _ _) H1 y Hy) as D. apply disjoint_decB_soundZ in D. unfold sivZ. cbn [fst snd]. lia.
  Qed.

  Lemma cross_disjB_sound : ltac2:(zQ "e0!k1!q0!hi9!q6!hkf!r3!it6!ht6!hl6!htc!hv7!hvd!itc!ig3>2l1@1$4$1>2l2@1$4$1>0@3$a$8@3$c@1$d?2fk^2^1$9>1x$1>1y$1>0@3$6$1^2^5>0@3$6$1^2^5@2$b@2$7@2$2?1E@3$5$0$0^4@2$2?1E@3$3$0$0^3@2$7@2$2?1E@3$5$0$0^3@2$2?1E@3$3$0$0^4").
  Proof.
    intros l1 l2 H x y Hx Hy. unfold cross_disjB in H.
    pose proof (proj1 (forallb_forall _ _) H x Hx) as H1. pose proof (proj1 (forallb_forall _ _) H1 y Hy) as H2.
    exact (disjoint_decB_soundZ x y H2).
  Qed.

End CheckSound.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STKS : ltac2:(zQ "10!q0$0") := ltac2:(zQ "82!t9!iub!le!qc!iv1!hkf!iv8!ive&@3$4@2$2$0$1@4$3$0$1+hgg0@1$6N6@1$7@2$2$0$1&@3$4@2$2$0$1@4$3$0$1+ogg0@1$6N0~0@4$3@2$2$0@1$5@2$2$0$1@2$2$0@1$5@2$2$0$1@4$3$0@1$5@2$2$0$1-ogggg0~1@4$3$0@1$5@2$2$0$1+vvvvvvogggg0~1").  (* [comment removed for export] *)
Definition HULLS : ltac2:(zQ "10!q0$0") := ltac2:(zQ "60!t9!le!iub!hkf!qc!ive@4$4@2$1$0@1$3@2$1$0$2@2$1$0@1$3@2$1$0$2@4$4$0@1$3@2$1$0$2+hggg0@1$5@2$1$0$2@4$4$0@1$3@2$1$0$2+nhmgg0@1$5@2$1$0$2").                   (* [comment removed for export] *)
Definition SHHS : ltac2:(zQ "10!q0$0") := ltac2:(zQ "60!t9!le!iub!hkf!qc!ive@4$4@2$1$0@1$3@2$1$0$2@2$1$0@1$3@2$1$0$2@4$4$0@1$3@2$1$0$2+nvvvngg0@1$5@2$1$0$2@4$4$0@1$3@2$1$0$2+hgggnvvvogg0@1$5@2$1$0$2").       (* [comment removed for export] *)
Definition placedB : ltac2:(zQ "40!hl6!hkf!q0!hq0>2bc$3>1l@1$1$2$0") := ltac2:(zQ "h00!k1!jg4!hs6!le!jgb!jh4!q6!hkf!r3!jm3!jmc!jn4!q0!hq0!hrb!jnc\2bc$d\1l@1$7$c@3$e@2$3$0$0\1s@2$3$0$0@2$1@2$1@2$1@2$1@3$5^3@1$4+hgg0@3$6$0$0^1@3$5^3@3$8$0$0^1@1$4@2$f+2+if@3$2^3^1$b@3$2^3^1$9@3$2^3^1$a^1").
End FPX2.

Section CheckSound2.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!hkf!phc@1$0$1").
  Variable E : ltac2:(zQ "10!td$0").
  Variable M : ltac2:(zQ "30!omb!ou1!ni2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable fk : ltac2:(zQ "20!hkf!nha@1$0$1").
  Hypothesis KN : ltac2:(zQ "10!pi7@4$0?4segs?1E?1M?2fk").
  #[local] Notation bc := (mkbc fk).
  Lemma placedB_sound : ltac2:(zQ "h20!k1!hi9!ht6!q6!r3!jo3!hvd!le!joa!hl6!hkf!htc!hv7!jp2!jpc!q0!ig3!jnc>1l@1$a$f>0@3$c$9@2$e@1$h0?2fk^1$b@3$d@2$7$0$0\1s@2$7$0$0@2$5@2$2+hgg0@2$1?1E@3$3$0$0^1@2$5@2$2@2$1?1E@3$4$0$0^1@2$h1+2+if@2$5@2$6@2$2@2$1?1E@3$4$0$0^1@2$1?1E@3$3$0$0$8@2$2@2$1?1E@3$4$0$0$8@2$1?1E@3$3$0$0^1@2$5@2$6@2$2@2$1?1E@3$4$0$0^1+hggg0@2$2+nhmgg0@2$1?1E@3$3$0$0^1@2$6@2$2@2$1?1E@3$4$0$0^1+nvvvngg0@2$2+hgggnvvvogg0@2$1?1E@3$3$0$0^1^2").
  Proof.
    intros l H. apply Forall_forall. intros s Hs. pose proof (proj1 (forallb_forall _ _) H s Hs) as H1.
    apply andb_prop in H1 as [H1 H4]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H1 as [H1 H2]. apply andb_prop in H1 as [H1 H5].
    rewrite le_linB_eqf in H1, H5. apply (le_lin_sound segs E M fk KN) in H1. apply (le_lin_sound segs E M fk KN) in H5. rewrite lconst_den in H1, H5.
    apply (disjoint_decB_soundZ segs E M fk KN) in H2. apply (disjoint_decB_soundZ segs E M fk KN) in H3. apply (disjoint_decB_soundZ segs E M fk KN) in H4.
    unfold HULLS, SHHS in H3, H4. cbn [fst snd] in H3, H4.
    change (lden E (65536, [])) with 65536 in H3. change (lden E (7430144, [])) with 7430144 in H3.
    change (lden E (2147446784, [])) with 2147446784 in H4. change (lden E (17594333495296, [])) with 17594333495296 in H4.
    repeat split; lia.
  Qed.
End CheckSound2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition KPSk : ltac2:(zQ "50!hl6!hkf!jq7!le!t9>1g$0@1$1@2$3$2$4") := ltac2:(zQ "h90!jq7!t9!le!iv1!qc!hl6!ive!jqd!hkf!jv1!jva!kg3!kgc!kh5!khe!ki7!kj0!kj9!kk2!kkb!kl4!kld!km6!kmf!kn8\1g$5@3$7@2$2$0$1@3$3@2$2$0$1@4$4$0$1$9+hggg0@3$3@2$2$0$1@4$4$0$1$a+jougg0@3$3@2$2$0$1@4$4$0$1$b+igggghhgg0@3$3@2$2$0$1@4$4$0$1$c+ogggg0@3$3@2$2$0$1@4$4$0$1$d+hgg0@3$3@2$2$0$1@4$4$0$1$e+hggg0@3$3@2$2$0$1@4$4$0$1$f+hgg0@3$3@2$2$0$1@4$4$0$1$h0+hgg0@3$3@2$2$0$1@4$4$0$1$h1+rgpgg0@3$3@2$2$0$1@4$4$0$1@1$h2^1+hgg0@3$3@2$2$0$1@4$4$0$1@1$h3^1+hgggg0@3$3@2$2$0$1@4$4$0$1@1$h4^1+ogggg0@3$3@2$2$0$1@4$4$0$1@1$h5^1+hgg0@3$3@2$2$0$1@4$4$0$1@1$h6^1+hgg0@3$3@2$2$0$1@4$4$0$1@1$h7^1+hgg0@1$6@2$2$0$1M5\1g$5@1$8@2$2$0$1^1@1$6@2$2$0$1@3$3@2$2$0$1@4$4$0$1$h8+igg0@1$6@2$2$0$1").
Definition ksiv : ltac2:(zQ "40!jq7!le!t9!q0>2kc@2$1$0$2$3") := ltac2:(zQ "90!jq7!t9!q6!k1!qc!le!r3!ko2!ko8\2kc@2$5$0$1@4$4$3$3@1$7@3$2$0$1^1@2$8@3$6$0$1^1@3$2$0$1^1").
Definition KPS : ltac2:(zQ "30!hl6!hkf!q0>1g$0@1$1$2") := ltac2:(zQ "80!hl6!jq7!le!ii2!t9!kt4!ktc!q0\1g$0@4$3@2$2$1$4$7$6@1$5^1").
Lemma KPSk_pos : ltac2:(zQ "80!jq7!t9!le!hl6!r3!jp2!kt4!ku4>1g$3@3$5@2$2$0$1\2kc@2$2$0$1@2$7Z@3$4$0$1^1@1$6^1").
Proof. intros [|]; repeat constructor. Qed.
Lemma ksiv_den : ltac2:(zQ "e1!t9!jq7!k1!q6!r3!hv7!kua!ktc!hi9!kv0!le!jo3!td!kv7&@2$9+hgg0@2$6^2@3$3$1$0^1>1E$c>2kc@2$a$1$0@2$b@3$5$0@2$8^2@3$3$2$2@1$7^1~0@3$5$0@2$8^2@3$4$2$2@1$7^1@2$d@3$4$1$0^1~0").
Proof. intros E [k c]. unfold ksiv, pg, pgo, lden. cbn [fst snd tden]. rewrite ?uE_var. lia. Qed.
(* [comment removed for export] *)
Definition KPSX : ltac2:(zQ "30!hl6!hkf!q0>1g$0@1$1$2") := ltac2:(zQ "c0!k1!hl6!q0!ive!le!jqd!iv1!hkf!qc!ko2!ko8!kve\1g$1@3$5$2@1$b^1M1\1g$1@1$7$2^1@3$6@2$4$0$0@4$8$0$0@1$9N5@2$a+igg0N5@1$3@2$4$0$0@1$3$2").
(* [comment removed for export] *)
Definition APPS : ltac2:(zQ "30!hl6!hkf!q0>1g$0@1$1$2") := ltac2:(zQ "h21!le!k1!t9!iub!hkf!jqd!ive!qc!lg5!hl6!iv1!lgf!ii2!lh9!li2!ko2!lib!q0&@2$0$1@2$0$2@1$4@2$0$2$3\1g$9@4$c@2$0$1$1$h1$h0@3$5@2$0$1$1@3$b@2$0$1$1N3@1$8^1@3$5@2$0$1$1@3$d@2$0$1$1N4@1$8^1@3$a~0@4$7$1@2$0$2@1$4@2$0$2$3@1$f$e@4$7$2@1$4@2$0$2$3+hgg0@1$6@2$0$2$3@1$6~0").   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LZS : ltac2:(zQ "40!hl6!hkf!jq7!q0>1g$0>3cls$2@1$1$3") := ltac2:(zQ "50!hl6!jq7!lj3!q0!lje\1g$0\3cls$1@2$4$3@1$2^2").   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vis_nwB : ltac2:(zQ "50!iub!hl6!hkf!le!hq0>2bc$4>1l@1$2@2$3$0$0$1") := ltac2:(zQ "90!iub!le!lk4!jg4!q6!hkf!r3!hq0!hrb\2bc$7\1l@1$5@2$1$0$0@3$8@2$1$0$0\1p@2$1$0$0@2$3@2$2^3@3$4$0$0^1@2$2^3@3$6$0$0^1^1").

Definition lz_check : ltac2:(zQ "30!hl6!jq7!lp2>1g$0>3cls$1>2ch$2$0") := ltac2:(zQ "i60!iub!le!k1!jg4!hl6!li2!jqd!iv1!ive!qc!lp9!lq4!lqa!iv8!jq7!htc!lt4!ltd!ko2!ko8!lu9!kve!lv1!lv9!mg0!irb!itc!jpc!mgb!q0!mh6!lp2!mhf!mib!mj7!mjc!hq0!ig3\1g$4\3cls$e\2ch$hf=2bc$i4@1$i5@1$hc@1$b^1@2$3@2$3@2$3@2$3@2$3@2$h9^1@1$h6^4@3$ha^1@1$h4^4@2$h7^4^3@2$hb^1@3$6$hd@1$h5^4@3$7@2$1$2$2@4$9$2$2@1$h2$5@2$h3+hgg0$5@1$8@2$1$2$2M4\1g$4$4^4@2$h1@1$b^2@3$i3@1$dN5+nh6+nvvv4$f@2$h8^1@3$6@2$1$0$0@1$he^2@1$a^2@4$i0@2$1$0$0$i1@1$a^2@3$7@2$1$0$0@4$9$0$0@3$i2$h0@1$c+hgg0@1$d$5@1$c+hgg0@1$8@2$1$0$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint evz (e : expr) (acc : list Z) : list Z :=
  match e with
  | ELit _ => acc
  | EVar w => Z.of_nat w :: acc
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evz a (evz b acc)
  | EExt _ _ _ a => evz a acc
  | EBlob _ _ _ _ => acc
  end.
Definition zmem : ltac2:(zQ "30!t9!hl6!hkf>1z$0>1l@1$2$0$1") := ltac2:(zQ "40!t9!hkf!mk4!mkf\1z$0\1l@1$1$0@3$2$0@1$3^2^1").
Definition zinter : ltac2:(zQ "30!hkf!t9!hl6>2l1@1$0$1>2l2@1$0$1$2") := ltac2:(zQ "40!t9!hkf!ml6!mk4\2l1@1$1$0\2l2@1$1$0@3$3$0\1z$0@2$2^1^2^2").
Definition lin_vz : ltac2:(zQ "30!hkf!t9!k1>1l$2@1$0$1") := ltac2:(zQ "90!t9!iub!le!r3!hkf!ive!mle!k1!mm5\1l$7@4$8@2$2$0$1$0\1t@2$2$0$1@2$6@3$3$0$1^1@1$5$0@3$3$0@1$4@2$2$0$1^1").
Definition lin_hasZ : ltac2:(zQ "40!hkf!t9!hl6!iub>2vl@1$0$1>1e$3>2ve@1$0$1$2") := ltac2:(zQ "92!iub!mn1!jq7!t9!hl6!hkf!mnb!mo4!htc&\2op$6\1a$0\1b$0@2$1^6^4&\2op$7\1a$0\1b$0@2$1^6^4\2vl@1$5$3\1e$0\2ve@1$5$3M0\1e$0$4^2\1z$3$8\1n$2@2$1^4^2~0~0~1~1\2sx$4\2lo$2\1n$2\2e0$0@2$1^7^5\2sx$4\1k$2\1i$3\1n$2@2$1^7^5").
Definition kdisj_preZ : ltac2:(zQ "40!hkf!t9!iub!hl6>2vx@1$0$1>2vr@1$0$1>2b1$2>2b2$2>3vb1@1$0$1>3vb2@1$0$1$3") := ltac2:(zQ "60!hkf!t9!mod!jg4!iub!mp9\2vx@1$0$1\2vr@1$0$1\2b1$4\2b2$4\3vb1@1$0$1\3vb2@1$0$1@2$5@2$3@3$2^6^4^2@3$2^5^3^1@2$3@3$2^6^3^1@3$2^5^4^2").

Lemma zeqb_of_nat : ltac2:(zQ "60!jq7!mpf!hl6!hv7!ms4!mkf>1v$0>1w$0@3$3$2@2$5@1$1^2@1$1^1@2$4^2^1").
Proof. intros v w. destruct (Z.eqb_spec (Z.of_nat v) (Z.of_nat w)) as [E|E]; destruct (Nat.eqb_spec v w) as [F|F]; try reflexivity; exfalso; lia. Qed.
Lemma zmem_evz : ltac2:(zQ "b0!ml6!mpf!hl6!hkf!jq7!mp9!hv7!t9!mle!iub!msb>1v$4>1e$9>3acc@1$3$7@3$6$2@2$0@1$1^3@2$8^2^1@2$5@2$a^3^2@2$0@1$1^3^1").
Proof.
  intros v e. induction e as [z|w|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros acc; cbn [evz mentions_var];
    try reflexivity; try (rewrite IHa, IHb; destruct (mentions_var v a); reflexivity); try (apply IHa).
  unfold zmem. cbn [existsb]. rewrite zeqb_of_nat. reflexivity.
Qed.
Lemma existsb_evz : ltac2:(zQ "b0!t9!mle!ive!ml6!iub!mk4!hl6!hkf!mp9!hv7!mt9>2e1$4>2e2$4>3acc@1$7$0@3$9$6@3$5$0\1z$0@2$3^1@2$1^4@1$2$0@2$1^2^1@2$8@2$a^3^2@3$5$0\1z$0@2$3^1@2$1^4@1$2$0^1").
Proof.
  intros e1 e2. induction e2 as [z|w|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros acc; cbn [evz shares_var];
    try reflexivity; try (rewrite IHa, IHb; destruct (shares_var e1 a); reflexivity); try (apply IHa).
  cbn [existsb]. rewrite zmem_evz. cbn [zmem existsb]. rewrite orb_false_r. reflexivity.
Qed.
Lemma existsb_flat_map : ltac2:(zQ "50!mk4!hl6!hkf!hv7!mm5>1AT>1BT>1f>0^1$1>1g>0^3@1$2^3>1l@1$2^4@3$3$1@3$0^4^3@4$4^5^4^2^1@3$0^5\1a^5@3$0^5^4@1^3^1^1").
Proof. intros A B f g l. induction l as [|a l IH]; [reflexivity|]. cbn [flat_map existsb]. rewrite existsb_app, IH. reflexivity. Qed.
Lemma existsb_ext' : ltac2:(zQ "40!hl6!hv7!mk4!hkf>1AT>1f>0^1$0>1g>0^2$0>1l@1$3^3>0>1a^4@3$1$0@1^4^1@1^3^1@3$1$0@3$2^5^4^2@3$2^5^3^2").
Proof. intros A f g l H. induction l as [|a l IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.
Lemma lin_has_Z : ltac2:(zQ "a0!hl6!ive!hv7!t9!mle!mod!mu5!muf!iub!k1>1l$9>1e$8@3$2$0@2$7^2^1@3$5@1$6^2^1@2$4^1@1$1$3").
Proof.
  intros l e. unfold lin_has, lin_hasZ, zinter, lin_vz. destruct e; try reflexivity;
    (rewrite existsb_flat_map; apply existsb_ext'; intros t; rewrite existsb_evz; cbn [existsb]; rewrite orb_false_r; reflexivity).
Qed.
Lemma kdisj_pre_Z : ltac2:(zQ "c0!k1!q6!ive!t9!mle!mu5!q0!iub!hl6!hv7!mv9!ng7>1x$6>1r$6>2b1$7>2b2$7@3$9$8@4$b^4^3^2^1@6$a@1$5@3$1$0$0^4@1$5@3$1$0$0^3^2^1@2$4^2@1$2$3@2$4^1@1$2$3").
Proof. intros. unfold kdisj_pre, kdisj_preZ. rewrite !lin_has_Z. reflexivity. Qed.

Definition kdp : ltac2:(zQ "00T") := ltac2:(zQ "50!le!hkf!t9!q0!iub@2$0@2$0@2$0@2$0@2$0$4$4@1$1$2@1$1$2$3$3").
Definition kdprep1 : ltac2:(zQ "40!hkf!nh3!nha!hq0>2bc$3>1K$2@1$0$1") := ltac2:(zQ "h33!le!k1!iub!t9!nh3!hkf!ive!ni2!nib!qc!nj2!nha!jq7!mle!r9!nja!nk5!iv1!hq0&@2$0@2$0@2$0$2$2@1$5$3@1$5$3&@2$0~0@2$0$1$1&@2$0~1@2$0$1$1\2bc$h2\1K$bMb\1K$b@1$5$4^1\1a$8\1w$c\1v$2@1$6$4\1a$8\1n$2@1$6$4\1a$8\1n$2\1k$c@1$6$4\2lo$3\2hi$3@1$6$4\1e$2\1m$3@1$6$4\1e$2\2lo$3\2hi$3@1$6$4\1a$8\1n$2@1$6$4\2a1$8\2n1$2\2a2$8\2n2$2M7\1x@1$7$1@1$5$4@2$f^6^4\2f1$1M7\1x@1$7$1@1$5$4@2$h0^7^4\2m1$1M7\1x@1$7$1@1$5$4@2$f^8^4\2f2$1M7\1x@1$7$1@1$5$4@2$h0^9^4\2m2$1@3$h1~2@4$9~1@2$0$1$1@4$9~0@2$0$1$1@4$9@2$0@2$0$2$2@1$5$3@1$5$3@4$9@2$0$2$2@1$5$3@4$9$2$2@1$a^8@1$a^6@2$d@1$a^8@1$6$3@2$d@1$a^6@1$6$3@4$9$1$1^4@2$e^4^3@4$9$1$1^2@2$e^2^1@1$6~2@1$6$4@1$6$4@1$6$4@1$6$4\1a$8\1n$2\1c$3@1$6$4\1a$8\1n$2@1$6$4").
Definition kdprep : ltac2:(zQ "30!hkf!nh3!hq0>2bc$2@1$0$1") := ltac2:(zQ "60!nh3!nl0!nha!nlb!hq0!mm5\2bc$4@4$5$2$0@1$1^1@1$3^1").
Definition sivz : ltac2:(zQ "00T") := ltac2:(zQ "40!hkf!le!t9!q0@2$1$3@1$0$2").
Definition mksz : ltac2:(zQ "20!nm4!q0>1x$1$0") := ltac2:(zQ "70!q0!k1!q6!hkf!qc!t9!mu5\1x$0@4$4$0@1$3$5^1@1$6@3$2$1$1^1").
Definition kdisjP1 (bc : bctx) (x r : sivz) (p : kdp) : bool :=
  let '(b1, b2, vb1, vb2, s1, s2) := p in
  if negb (kdisj_preZ (snd x) (snd r) b1 b2 vb1 vb2) then false
  else (insideB bc (fst x) (fst s1) (snd s1) && insideB bc (fst r) (fst s2) (snd s2)) || (insideB bc (fst x) (fst s2) (snd s2) && insideB bc (fst r) (fst s1) (snd s1)).
Definition disjoint_decP : ltac2:(zQ "50!nm4!hl6!hkf!nh3!hq0>2bc$4>4prep@1$2$3>1x$0>1r$0$1") := ltac2:(zQ "d0!k1!q6!hkf!t9!q0!mp9!r3!nh3!nm4!jh4!nmc!hq0!mk4\2bc$b\4prep@1$2$7\1x$8\1r$8@2$5@2$5@3$9^4@3$6$0$0@3$1$4@1$2$3^2@3$1$0$0@3$1$4@1$2$3^1@3$9^4@3$6$0$0@3$1$4@1$2$3^1@3$1$0$0@3$1$4@1$2$3^2@3$c$7@3$a^4^2^1^3").
Fixpoint all_pairs_disjP (bc : bctx) (prep : list kdp) (l : list sivz) : bool :=
  match l with [] => true | x :: r => forallb (fun y => disjoint_decP bc prep x y) r && all_pairs_disjP bc prep r end.
Definition cross_disjP : ltac2:(zQ "50!hkf!nm4!hl6!nh3!hq0>2bc$4>4prep@1$0$3>2l1@1$0$1>2l2@1$0$1$2") := ltac2:(zQ "60!nm4!hkf!hrb!nn7!nh3!hq0\2bc$5\4prep@1$1$4\2l1@1$1$0\2l2@1$1$0@3$2$0\1x$0@3$2$0\1y$0@4$3^6^5^2^1^2^2").
Definition placedP : ltac2:(zQ "50!hkf!hl6!nh3!nm4!hq0>2bc$4>4prep@1$0$2>1l@1$0$3$1") := ltac2:(zQ "h30!k1!hkf!le!jg4!t9!nm4!q6!nn7!no8!jgb!jh4!r3!nh3!np0!np9!joa!hq0!hrb!jnc\2bc$h0\4prep@1$1$c\1l@1$1$5=2S1$5@1$8$f=2S2$5@1$8$d=2S3$5@1$8$e@3$h1@2$2@2$2$0$0@1$1$4\1s@2$2@2$2$0$0@1$1$4@2$3@2$3@2$3@2$3@3$a^7@1$9+hgg0@3$6$0$0@3$6@2$2$0$0@1$1$4^1@3$a^7@3$b$0$0@3$6@2$2$0$0@1$1$4^1@1$9@2$h2+2+if@4$7^7^6^1^4@4$7^7^6^1^3@4$7^7^6^1^2^4").

Lemma kdisjP1_eq : ltac2:(zQ "b0!no8!q0!hl6!hv7!nmc!nh3!nl0!nq1!nha!hq0!mk4>2bc$9>1x$1>1r$1>1K$8@3$3$2@3$a$5@3$4^4@1$0^3@1$0^2@2$6^4^1@4$7^4^3^2^1").
Proof.
  intros bc x r K. destruct K; try reflexivity. cbn [kdprep1 kdisj1B]. rewrite kdisj_pre_Z.
  repeat match goal with |- context [match ?o with Some _ => _ | None => _ end] => destruct o end;
    cbn [existsb kdisjP1 mksz fst snd]; rewrite ?orb_false_r; try reflexivity;
    match goal with |- context [negb ?b] => destruct b end; reflexivity.
Qed.
Lemma disjoint_decP_eq : ltac2:(zQ "80!no8!q0!hl6!hv7!nn7!nqb!hs6!hq0>2bc$7>1x$1>1r$1@3$3$2@4$4^3@1$5^3@1$0^2@1$0^1@3$6^3^2^1").
Proof.
  intros bc x r. unfold disjoint_decP, disjoint_decB, kdisjB, kdprep. cbn [mksz fst snd]. f_equal.
  rewrite existsb_flat_map. apply existsb_ext'. intros K. apply kdisjP1_eq.
Qed.
Lemma forallb_map' : ltac2:(zQ "50!hl6!hrb!hkf!hv7!ii2>1AT>1BT>1f>0^1$0>1g>0^3^3>1l@1$2^4@3$3$0@3$1^4^3@4$4^5^4^2^1@3$1^5\1a^5@1^4@1^3^1^1").
Proof. intros A B f g l. induction l as [|a l IH]; [reflexivity|]. cbn [map forallb]. rewrite IH. reflexivity. Qed.
Lemma forallb_ext' : ltac2:(zQ "40!hl6!hv7!hrb!hkf>1AT>1f>0^1$0>1g>0^2$0>1l@1$3^3>0>1a^4@3$1$0@1^4^1@1^3^1@3$1$0@3$2^5^4^2@3$2^5^3^2").
Proof. intros A f g l H. induction l as [|a l IH]; [reflexivity|]. cbn [forallb]. rewrite H, IH. reflexivity. Qed.
Lemma all_pairs_disjP_eq : ltac2:(zQ "b0!q0!hl6!hkf!hv7!ii2!nr5!nqb!no8!nm4!irb!hq0>2bc$a>1l@1$2$0@3$3$1@3$5^2@1$6^2@4$4$0$8$7^1@2$9^2^1").
Proof.
  intros bc l. induction l as [|x l IH]; [reflexivity|]. cbn [map all_pairs_disjP all_pairs_disjB]. rewrite IH, forallb_map'. f_equal.
  apply forallb_ext'. intros y. apply disjoint_decP_eq.
Qed.
Lemma cross_disjP_eq : ltac2:(zQ "b0!q0!hkf!ii2!no8!nm4!hl6!hv7!ns8!nqb!itc!hq0>2bc$a>2l1@1$1$0>2l2@1$1$0@3$6$5@4$7^3@1$8^3@4$2$0$4$3^2@4$2$0$4$3^1@3$9^3^2^1").
Proof.
  intros bc l1 l2. unfold cross_disjP, cross_disjB. rewrite forallb_map'. apply forallb_ext'. intros x. rewrite forallb_map'.
  apply forallb_ext'. intros y. apply disjoint_decP_eq.
Qed.
Lemma placedP_eq : ltac2:(zQ "b0!q0!hl6!hkf!hv7!ii2!nqb!no8!nt7!nm4!jpc!hq0>2bc$a>1l@1$2$0@3$3$1@3$7^2@1$5^2@4$4$0$8$6^1@2$9^2^1").
Proof.
  intros bc l. unfold placedP, placedB. cbv zeta. rewrite forallb_map'. apply forallb_ext'. intros s. cbn [mksz fst snd].
  fold (mksz s). rewrite !disjoint_decP_eq. reflexivity.
Qed.

Definition lz_checkP : ltac2:(zQ "30!hl6!jq7!lp2>1g$0>3cls$1>2ch$2$0") := ltac2:(zQ "ic0!iub!le!k1!jg4!q0!hl6!ii2!no8!nm4!li2!jqd!iv1!ive!qc!lp9!lq4!lqa!iv8!hkf!jq7!htc!lt4!ltd!ko2!ko8!lu9!kve!lv1!lv9!nr5!ns8!nh3!nqb!nt7!mg0!mgb!mh6!lp2!mhf!mib!mj7!mjc!hq0!ig3\1g$5\3cls$h3\2ch$i5=2bc$ia@1$ib@1$i3@1$f^1=4prep@1$h2$hf@1$i0^1@2$3@2$3@2$3@2$3@2$3@3$hd^2^1@4$6$4$8$7@1$hb^5@4$he^2^1@4$6$4$8$7@1$h9^5@4$6$4$8$7@2$hc^5^4@3$i1^2^1@4$6$4$8$7@3$a$4@1$ha^5@3$b@2$1$2$2@4$d$2$2@1$h7$9@2$h8+hgg0$9@1$c@2$1$2$2M5\1g$5$5^5@2$h6@1$f^3@3$i9@1$h1N5+nh6+nvvv4$h4@2$i2^2@3$a@2$1$0$0@1$i4^3@1$e^3@4$i6@2$1$0$0$i7@1$e^3@3$b@2$1$0$0@4$d$0$0@3$i8$h5@1$h0+hgg0@1$h1$9@1$h0+hgg0@1$c@2$1$0$0").
Lemma lz_checkP_eq : ltac2:(zQ "60!hl6!jq7!hv7!nu2!nue!lp2>1g$0>3cls$1>2ch$5@3$2$0@3$4^3^2^1@3$3^3^2^1").
Proof. intros g cls ch. unfold lz_checkP, lz_check. cbv zeta. rewrite all_pairs_disjP_eq, cross_disjP_eq, placedP_eq. reflexivity. Qed.

Lemma HS_lz_check : ltac2:(zQ "b0!lp2!hv7!nvb!hl6!jq7!ni2!htc!og2!oh0!nu2!olf>1h$4>2ch$0>0@3$1@1$5$0@1$a^2@2$2$0^1@3$1$3@3$9@1$8^3@1$7^3^2$6").
Proof.
  intros h ch Hh. apply hs_lookup_cases in Hh. cbn [HSF_asan_table fold_right fst snd] in Hh.
  do 6 (destruct Hh as [[-> ->]|Hh]; [rewrite <- lz_checkP_eq; vm_cast_no_check (@eq_refl bool true)|]).   (* [comment removed for export] *)
  destruct Hh.
Qed.

Lemma vis_nwB_sound : ltac2:(zQ "h70!iub!t9!le!hkf!q6!qc!r3!hv7!ii2!omb!or6!orc!hi9!ou1!hl6!ni2!htc!phc!mg0!td!nha!ig3!pi7>4segs@1$3$h1>1E$h3>1M>0@1$d@1$9#k0@1$f@1$d@1$9#8>2fk@1$3$h4>1l@1$3@2$2$0$0>0@4$h6^5^4^3^2>0@3$7$e@2$h2@1$h5^3^2$h0@3$7@1$3@2$2$1$1@4$8@2$2$0$0@2$2$1$1\1p@2$2$0$0@4$5$1$1@2$a^7@3$4$0$0^1@2$a^7@3$6$0$0^1^3@4$8@2$2$0$0@2$2$1$1\1p@2$2$0$0@4$5$1$1@2$c^7@1$b@3$4$0$0^1@2$c^7@1$b@3$6$0$0^1^3").
Proof.
  intros segs E M fk l KN H. apply map_ext_in. intros p Hp.
  pose proof (proj1 (forallb_forall _ _) H p Hp) as H1. apply andb_prop in H1 as [H1 H2]. rewrite lin_nowrapRB_eqf in H1, H2.
  unfold uE. rewrite (lin_nowrapR_sound segs E M fk _ KN H1), (lin_nowrapR_sound segs E M fk _ KN H2). reflexivity.
Qed.
End FPX3.
(* [comment removed for export] *)
