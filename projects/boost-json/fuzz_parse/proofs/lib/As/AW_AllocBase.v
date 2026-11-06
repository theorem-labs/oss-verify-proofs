(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list04Npos35stdpp9bitvectorbdefinitionsk12bvhc3app37Corelib5Lists7ListDefm96repeat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~o92b846Stdlib6ZArith6BinInt1Zs93divs93subs96to_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~v69shadow_of69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~hk08round_up37Corelib4Init5Logichod3andhod2eqs92les92lts96modulohc4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hs84cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~igc5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~il08rw_cellshc3nilhc6optionhs82C1hs82CBs93pows94land79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~irf7d_putidirf5d_idsirf4d_wfirf5depots93adds93lor89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_AllocBase3HCW~~~~~~jj06hb1_ofjj05b1_okhc6lengthjj0apre_shadows96of_natk1bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjr7dmachine_state3h5LinuxProcessSemantics5Riscv7Preludejvf5bvmapv63memhod2exhc4prodhc4pairhc4None79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~kkf5u8arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kp23mkRkp25munchkp23stkkp25wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~kue2MSkue6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ljb7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~lo07seg_romo92wzhs82C8s93mulv65aceilhod2orm93mapigccASHADOW_BASEjj0cpoison_postK79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~mgfaACANPOISONmgf7ACFLAGSmgf7AGOT_LOmgf9AGOT_VALSmgfbAHIGHMEMENDmgf7AMEMSETmgfbAREALMEMSETmgfcASHBASE_CELLv66AHI_LOv69ALOWSH_LOv62sh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~mt13evtk17Z_to_bvkp23ivlhs82C4s93min79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_AllocBase~~~~~~nj0calloc_shadownj05b1_oknj0ekAllocBegMagicmgf5wlistirf5DEPOTkkf6u32arrhs82C236Stdlib5Lists4Listnrf3revnrf2tlmgf5AINSTm96Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAW_Combined~~~~~~nv1h1combined_hit_postmgfbCACHE_STATSmgfbOI_SPACEBEGmgf5akobjhk08class_idhk0aclass_sizehk08kMaxSizehk0akSpaceSizehk04zlen" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition kAllocBegMagic : Z := 0xCC6E96B9CC6E96B9.

(* [comment removed for export] *)
Definition alloc_shadow : ltac2:(zQ "40!h9!j4!jb!le>2rz$0>4size$0>3csz$0@1$1@1$3@1$2#8") := ltac2:(zQ "b0!jb!le!h9!m3!o0!s4!u1!u7!ud!hj4!ho1\2rz$2\4size$2\3csz$2@3$3@1$1@1$0#8@3$4@1$1@1$0#8@1$5+va@1$8@2$6^3+8@3$3@1$1@1$0#8@1$9^2@3$4@1$1@1$0#8@1$5+va@1$8@2$6@2$7@2$7^1^3@2$a^2+8+8").
(* [comment removed for export] *)
Definition b1_ok : ltac2:(zQ "10!h9>1b$0P") := ltac2:(zQ "60!hq1!h9!hq8!hqe!hr3!hr8\1b$1@2$0@2$0@2$3Z^1@2$4^1+hg0@3$2$1@2$5^1+o0+h1").

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_CB1 : ltac2:(zQ "c0!jb!le!hs1!ig4!ik7!iob!j4!ip7!ipd!h9!iq6!iqc>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$9>1b@1$1@1$0#8>2cs@1$6$3>0@4$5$4^4^3@3$2$3@2$bN1@3$2@1$1@1$0#8^2@1$7@1$1@1$0#8^1@4$5$4^5^4@3$2$3@1$a^3^2").
Proof. intros m A b cs [[[_ W] B] R]. exact (conj (conj (conj I W) B) R). Qed.

(* [comment removed for export] *)
Lemma land_mask_down : ltac2:(zQ "90!h9!ir2!hqe!hq1!u7!hq8!ir8!hr3!hr8>1x$0>1k$0>1j$0>0@2$3@2$2Z^3@2$7^3@2$1+2^2>0@2$3@2$2Z^2@2$2^2^3@3$5$0@2$6^5@2$4@2$1+2^4@2$1+2^3@2$4^5@2$8^5@2$1+2^3").
Proof.
  intros x k j Hx Hj.
  replace (2^k - 2^j)%Z with (Z.ldiff (Z.ones k) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^k)%Z with (2^j * 2^(k-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (0 < 2^(k-j)) by (apply Z.pow_pos_nonneg; lia). assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (k - j))))%Z with ((2^(k-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2^j)%Z ltac:(hci; lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma land_m48_8 : ltac2:(zQ "90!h9!hq1!hq8!ir8!hqe!hr3!hr8!ir2!u7>1x$0>0@2$1@2$4Z^1@2$5^1@2$7+2+j0@3$2$0@2$3^2+vvvvvvvvvvv8@2$8^2@2$6^2+8").
Proof. intros x Hx. change 281474976710648 with (2^48 - 2^3). rewrite land_mask_down by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma d_putid_range : ltac2:(zQ "90!ivf!hr3!hq1!h9!jga!jh3!jhb!ji4!hqe>1d$6>1h$3>0@1$5^2>0@2$1@2$7@1$4^3+1+hggg0@2$2@2$8+1@2$0^4^3@2$1@2$0^4^3+hggg0").
Proof.
  intros d h WF CAP. unfold d_putid. pose proof (wf_ids d WF).
  destruct (Z.eqb_spec (d_find d h) 0) as [E0|NE]; [lia|].
  pose proof (d_find_range d h WF NE). lia.
Qed.

(* [comment removed for export] *)
Definition hb1_of : ltac2:(zQ "10!h9>1o$0$0") := ltac2:(zQ "60!jia!h9!ir8!hr8!ir2!u7\1o$1@2$0@2$2@2$0@2$5^1@2$3^1@2$4+2+2+1+of+h0").
Lemma hb1_facts : ltac2:(zQ "70!hq1!jn6!hqe!hr3!h9!jo0!ir8>1o$4>0@2$0@2$2Z^1@2$3^1+hg0@2$0@2$0@2$2Z@1$1^2@2$3@1$1^2+hg0@1$5@2$6@1$1^2+v3").
Proof.
  intros o Ho.
  pose proof (forall_rangeZ_spec (fun o => let v := hb1_of o in
       (0 <=? v) && (v <? 256) && (0 <=? Z.land v 243) && (Z.land v 243 <? 256) && (Z.land v 243 mod 128 =? 17)) 0 256 o) as C.
  cbn beta in C. specialize (C ltac:(hci; vm_compute; reflexivity) ltac:(hci; lia) ltac:(hci; lia)).
  cbn zeta in C. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt, Z.eqb_eq in C. unfold b1_ok. lia.
Qed.

(* [comment removed for export] *)
Definition pre_shadow : ltac2:(zQ "40!h9!j4!jb!le>3rz8$0>2q8$0>4csz8$0@1$1@1$3@1$2#8") := ltac2:(zQ "80!jb!le!o0!h9!s4!ud!m3!u7\3rz8$3\2q8$3\4csz8$3@3$6@1$1@1$0#8@3$2@1$1@1$0#8@1$4+va@1$5^3@3$6@1$1@1$0#8@3$2@1$1@1$0#8@1$4Z@1$5^2@3$2@1$1@1$0#8@1$4+va@1$5@2$7@2$7^1^3^2").
Lemma pre_shadow_length : ltac2:(zQ "90!h9!hqe!jo9!hq8!jb!jp2!ji4!jq0!le>3rz8$0>2q8$0>4csz8$0>0@2$1Z^3>0@2$1Z^3>0@2$1@2$6^5^4^3@3$3$0@1$7@2$2@1$8@1$4#8@3$5^6^5^4^4").
Proof. intros. unfold pre_shadow. rewrite !length_app, !repeat_length. lia. Qed.
Lemma pre_shadow_0 : ltac2:(zQ "b0!jb!h9!hqe!le!j4!hq1!hq8!o0!jp2!s4!ud>3rz8$1>4csz8$1>0@2$5@2$2Z^2@2$2^2^1@3$6@1$4@1$3@1$0#8@3$8^3Z^2@3$7@1$3@1$0#8@1$9+va@1$a^2").
Proof.
  intros rz8 csz8 H. unfold pre_shadow. change (repeat (b8 0) (Z.to_nat 0)) with (@nil byte). rewrite app_nil_l, Z.sub_0_r.
  rewrite <- repeat_app. f_equal. lia.
Qed.
Lemma rw_cells_C1 : ltac2:(zQ "c0!jb!le!hs1!ig4!ik7!iob!j4!ip7!ipd!h9!iq6!iqc>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$9>1b@1$1@1$0#8>2cs@1$6$3>0@4$5$4^4^3@3$2$3@1$a^2^1@4$5$4^5^4@3$2$3@2$bN1@3$2@1$1@1$0#8^3@1$7@1$1@1$0#8^2").
Proof. intros m A b cs [[[_ W] B] R]. exact (conj (conj (conj (eq_refl _) W) B) R). Qed.
Lemma b8_of_byte : ltac2:(zQ "50!jb!le!hq8!s4!jq9>1b@1$1@1$0#8@3$2@1$1@1$0#8@1$3@2$4@1$0#8^1^1").
Proof. intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Definition poison_postK : ltac2:(zQ "60!jb!le!h9!jue!ki5!kie>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$5>2lo$2>3shA$2>1k$2>1v$2>0$3P") := ltac2:(zQ "hf1!jb!le!kj4!h9!hq1!ik7!kja!jq9!hs1!ipd!kk1!jue!kk8!ip7!hq8!o0!ki5!kie!ko9!kse!kt5!kte!ku5!lib!lj1!ln5!lrf!s4!ji4!u7!ud&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h0@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$h1\2lo$3\3shA$3\1k$3\1v$3\3ms'$b@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$4@3$e$b^h1@7$h7@hf$h3^i8^i7^i6^i5^h0^f^e^i4^i3^d^c^b^a^9^8^7^6^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^5^4^3^2^h8@1$h8^i8^h7@1$c@1$1@1$0#k0^1@1$ha$5@2$4@3$h4@3$8@2$6$3$3@4$a$3$3@2$hd@2$7@1$0#k0^i7+k0@2$7@1$0#k0^i7@3$8@2$6$3$3@4$a$3$3^h4@2$hc^h4^h3@1$d@2$6$3$3^h6^1@2$4@3$h6$5^h6^1@2$4@2$h9$5^1@2$4@4$h5$5^1^h5@2$7@1$0#k0^i7@4$h2$5^1^h4@3$f@1$1@1$0#8@1$hb^h2@1$he^h3").

Lemma poison_shadow_specK : ltac2:(zQ "j40!jb!le!ig4!ik7!h9!lsa!hqe!hs1!lsf!hq8!iob!ip7!hq1!ji4!lt5!ltb!jq9!kk8!jo9!j4!lu3!lu9!ki5!luf!lvf!mkd!mlb!mm6!mn1!mne!mod!mp8!mq7!mr7!ms0!kie!msc!ko9!iq6!ngc!kse!kte!lib!ln5!lrf!s4!hr3!hr8!jq0!ir2!u7!nh3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$i3>2lo$4>4addr$4>3shA$4>1k$4>1v$4>3sbs@1$h3@1$1@1$0#8>0@2$ib$3^7>0@4$i9$3^8^7@2$h0@1$0#k0^i8>0@2$6@1$f?5HCEIL^8>0@2$6@2$d^9+k0@2$h0@1$0#k0^ia>0@3$9@1$1@1$0#k0^i3@1$5^9>0@3$9@1$1@1$0#k0^i3@1$5@2$e+8^8>0@3$9@1$1@1$0#k0^i3@1$5^8>0@3$9$4^b@1$i4^c>0@2$c@2$h4@2$6$i1^d@2$c@2$6Z^d@2$6@2$d^d@2$e+8^b$i2@2$c@2$6+1^b@2$c@2$6@2$d^d@2$e+8^b@1$f?5HCEIL@3$9$4@2$if^d+8Z>0@2$c@2$6Z^b@2$ie^b+hg0>0@4$i5$3^h1^e^b>0@3$9$4@1$j0@2$h2@1$1@1$0#8^c^e>0@4$a$3^h3$h9@3$7$2@1$i6@1$id+1@1$b$2>0@4$a$3^h4$hb@4$h5$4$2\1v$4@1$8@1$5^1$hc>0@4$a$3^h5$i0@3$7$2@1$8@1$5$h7@1$b$2>0@4$a$3^h6$hd@3$7$2@1$8@1$5@2$j2@2$j1+2+if+1@3$7$2@1$8@1$5Z@3$7$2@1$8@1$5Z@1$b$2>0@4$a$3^h7@2$d$ha+n8@3$7$2@1$8@1$5+vvvvvvvvvvvvvvvf@1$b$2>0@4$a$3^h8$hf@3$7$2@1$8@1$5$he@1$b$2@3$i7$3@h7$h8^ja^j9^j8^j7^j3^j2^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hb^ha^h9^h8^h6^h5^h4@7$ia@hf$i8^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb@2$j3@1$0#k0+phunc^ha@1$h1@1$1@1$0#k0^h9@1$ic$3").
Proof.
  intros until sbs. intros MI ST LO HI Ha0 Ha1 Ha2 HshA AR VR SH SHL CCAN GOT CSHB CHME CTHR CRMS. subst shA.
  assert (K8 : 8 * k / 8 = k) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  eapply evt_mono.
  - eapply (poison_shadow_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo addr (8 * k) v sbs); try eassumption.
    + ndestruct AR as (ARS & K1 & ARC & AR8). split; [| repeat split; try lia; rewrite Z.mul_comm; apply Z.mod_mul; lia].
      destruct ARS as [H|H]; [left| right]; lia.
    + rewrite K8. exact SHL.
  - intros ms' PO. unfold poison_post, poison_postK in *. rewrite K8 in PO.
    ndestruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & MU & WM & MI' & ST' & PZ).
    unfold poisoned, SHAD, poison_bytes in PZ. ndestruct PZ as (_ & _ & U8).
    neexists 16. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact U8].
Qed.

End HCW.


(* [comment removed for export] *)
Ltac lia_with_neg H := (repeat match goal with Hq : ~ _ |- _ => tryif constr_eq H Hq then fail else clear Hq end); lia.
Ltac sub_fp_struct :=
  let x := fresh "ox" in let Hx := fresh "OX" in
  unfold sub_fp; cbn [outside fst snd]; intros x Hx;
  repeat (lazymatch type of Hx with _ /\ _ => let H := fresh "OW" in destruct Hx as [H Hx] end);
  repeat (lazymatch goal with |- _ /\ _ => split end);
  (* [comment removed for export] *)
  first [ assumption | exact I | match goal with H : ~ _ |- _ => lia_with_neg H end | lia ].

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_struct | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac post_callDep segs m :=
  let ms := fresh "ms" in let PO := fresh "PO" in
  intros ms PO; unfold put_post, depot_W in PO;
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms PO; post_call segs m.
Tactic Notation "callDep" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callDep segs m ]
  end.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Record AENV (tp : word) (TSD CTX TH sb SO : Z) (T : list Z) (rest : list word) (m : mem) : Prop := mkAENV {
  e_tsdi : rw_cells asegs m 1833632 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)];          (* [comment removed for export] *)
  e_tp   : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)];
  e_tsd  : rw_cells asegs m TSD [C8 (wz CTX)];
  e_ctx  : rw_cells asegs m (CTX + 152) [C8 (wz TH)];
  e_lsan : rw_cells asegs m (bv_unsigned tp + 16) [C4 (wz 0)];
  e_got2 : rw_cells asegs m 0x1b61f8 [C8 (wz 0x10)];
  e_thr  : rw_cells asegs m TH [C8 (wz CTX)];
  e_tid  : rw_cells asegs m (CTX + 8) [C4 (wz 0)];
  e_init : rw_cells asegs m 1838872 [C1 (b8 1)];                                                (* [comment removed for export] *)
  e_afl  : rw_cells asegs m 2368672 [C1 (b8 0); C1 (b8 1); C1 (b8 0)];                          (* [comment removed for export] *)
  e_can  : rw_cells asegs m 1833628 [C1 (b8 1)];                                                (* [comment removed for export] *)
  e_got  : rw_cells asegs m 1791352 (map (fun v => C8 (wz v)) AGOT_VALS);                        (* [comment removed for export] *)
  e_shb  : rw_cells asegs m 1835576 [C8 (wz 2147450880)];                                       (* [comment removed for export] *)
  e_hme  : rw_cells asegs m 1838880 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];            (* [comment removed for export] *)
  e_thresh : rw_cells asegs m 2432480 [C8 (wz 0xffffffffffffffff)];                                        (* [comment removed for export] *)
  e_rms  : rw_cells asegs m 1799584 [C8 (wz 1727016)];                                          (* [comment removed for export] *)
  e_fill : rw_cells asegs m 1825380 [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)];                    (* [comment removed for export] *)
  e_part : rw_cells asegs m 1825421 [C1 (b8 1)];                                                (* [comment removed for export] *)
  e_hooks : rw_cells asegs m 2432256 (repeat (C8 (wz 0)) 10);                                    (* [comment removed for export] *)
  e_inst1 : rw_cells asegs m 1821688 [C8 (wz sb)];                                              (* [comment removed for export] *)
  e_inst2 : rw_cells asegs m 1825272 [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]];  (* [comment removed for export] *)
  e_so   : rw_cells asegs m SO [C8 (wz (SO + 16)); C8 (wz (Z.of_nat (length T)))];              (* [comment removed for export] *)
  e_tr   : u64arr asegs m (SO + 16) (map wz T ++ rest)
}.

End HCW2.


Ltac open_env E :=
  destruct E as [Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr];
  unfold AGOT_VALS in Egot; cbn [map] in Egot; cbn [repeat] in Ehooks.

(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition allocate_post : ltac2:(zQ "90!jb!le!h9!j4!jue!ki5!jhb!kie!nhd>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$7>1W@1$3$8>2lo$2>4size$2>2AB$2>1U$2>2rz$2>3csz$2>1P$2>3cnt$2>2mc$2>2TH$2>2id$2>6chunks@1$3$2>2d'$6>0$4P") := ltac2:(zQ "j31!jb!le!kj4!hq1!h9!ig4!ik7!ji4!hs1!lsa!lsf!kte!ip7!iob!ni4!s4!j4!ipd!hq8!jue!ko9!iq6!nia!u7!kk8!lu3!o0!ki5!nn2!no2!nob!npd!nq6!jhb!kie!msc!nqf!nr9!nhd!kse!kt5!ku5!lib!lj1!ln5!lrf!nt2!nt9!lt5!ud!jq9&>0@1$1@1$0#k0@1$h1@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$hb@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$i2\1W@1$h0$i6\2lo$4\4size$4\2AB$4\1U$4\2rz$4\3csz$4\1P$4\3cnt$4\2mc$4\2TH$4\2id$4\6chunks@1$h0$4\2d'$i1\3ms'$h3@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2@1$1@1$0#k0\2j0@1$1@1$0#k0@2$2@1$1@1$0#k0\2j1@1$1@1$0#k0@2$2@1$1@1$0#k0\2j2@1$1@1$0#k0@2$2@1$1@1$0#k0\2j3@1$1@1$0#k0@2$2$4\2b1$4@2$2~0\2m'~0@2$3@3$h2$h3^h5@7$ia@hf$i7^j6^j5^j4^j3^h4^h3^h2^j2^j1@1$9^hf^h1^h0^f^e^d^c^b^j0^if^ie^id^ic^ib^ia^i9^i8^i7^a^9^8^7^i6@1$ib^j6^i5@1$h8@1$1@1$0#k0^1@1$id$6@2$3@3$i8^i3^i4^1@2$3@3$i9$6^i4^1@2$3@2$ic$6^1@2$3@4$b$6^1^i2@2$j2@1$0#k0^j5@2$3@4$d$6^1^hc@3$8$5@1$e@1$9@2$h7^hb+1@3$8$5@1$e@1$9^ha@1$c$5@2$3@4$i4$6^1@2$7^hc+h0@1$hf@2$ie$4@2$if$4^h7@2$3@4$b$6^1@2$7@2$7^hc+h0@2$j0+4@2$h7^hb+1@2$7^hc+l0@2$3@4$d$6^1@2$7@2$7^h9+t0+qg0@3$8$5@1$a^6@3$8$5@1$a^5@3$8$5@1$a^4@3$8$5@1$a^3@1$c$5@2$3@4$d$6^1@2$7^hf-h0@3$8$5@1$h5@1$f+2@3$8$5@1$h5@1$f^2@3$8$5@1$i5@1$9Z@3$8$5@1$e@1$9^i1@3$8$5@1$a@1$9^h8@1$c$5@2$3@1$hd^2@2$3@2$h9@3$h2$4^he+h0@2$3@4$d$6^1^i0@3$8$5@1$a@1$9$he@3$8$5@1$a@1$9@2$7^hf-h0@1$c$5@4$b$6^1@2$7^i0+h0@2$7^hf-h0@2$3@4$h4$6^1^hf@3$ha@1$1@1$0#8@1$f+re@1$j1@2$h6^i1+hgg0@2$3@4$b$6^1@2$7^hf@2$h6^i1+hgg0@2$7^i0^hd@2$3@4$h4$6^1@1$i3^i0@3$hc^he^i1^hd@2$3@4$b$6^1@2$7^h9+qv0@2$7^h9+sm0@3$i0$6^h6^1").


(* [comment removed for export] *)
Lemma combined_hit_specP : ltac2:(zQ "ie0!jb!le!h9!ig4!ji4!hq8!ik7!hqe!hs1!lsa!hq1!lsf!ip7!iob!ltb!jq9!ntf!ni4!kte!hr8!lt5!kk8!j4!nu8!ki5!oj2!ok8!ol7!om6!npd!kie!omf!onb!oo9!op5!oq3!nqf!ngc!kse!lib!ln5!lrf!nt2!hr3!ir2!nh3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h8@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$he>2lo$2>4size$2>2CA$2>2sb$2>3cnt$2>2mc$2>6chunks@1$h6$2>2j0@1$1@1$0#k0>2j1@1$1@1$0#k0>2j2@1$1@1$0#k0>2j3@1$1@1$0#k0>1c$2>1P$2>3csz$2>0@3$5$2^3@1$hf^d>0@3$5$2^3@2$4^d@2$h4+l0^4>0@3$5$2^3@1$i0^5>0@2$i8$6^h2>0@4$h2$6^h3^h2@2$f@1$0#k0^j3>0@2$7@1$e?5HCEIL^h3>0@2$7@2$4^h4+j0@2$f@1$0#k0^j5>0@3$5$2@2$h3@2$f@1$0#k0^j6+h0Z>0@3$5@1$1@1$0#k0^if@1$9$h0>0@3$5@1$1@1$0#k0^if@1$9^h5>0@3$5@1$1@1$0#k0^if@1$9^h7>0@3$5@1$1@1$0#k0^if@1$9+8>0@2$a@2$7+h1^h9@2$7^h9$i1>0@2$a@3$hc?5HCEIL^h9+qi0@2$a@2$7@2$4^h9+qi0@1$e?5HCEIL@3$5$2@2$h3^h9+h0Z>0@2$a@2$7Z^h9@2$7@2$4^h9$i2@1$e?5HCEIL>0@4$d$6^he@2$4$h0$hb@3$8$3@1$b@1$9^ha@1$c$3>0@4$d$6^hf^h2@3$8$3@1$h1@1$9^ha@3$8$3@1$h1@1$9^h9@1$c$3>0@4$d$6^i0@2$4^h3+8@3$8$3@1$b@1$9^h2@1$c$3>0@4$i4$6^i1@2$4^h4+h0@1$hd@2$ia$2^ha>0@3$5$2^hd@2$i3$2^hb>0@2$a@2$7+1^he@2$7^he+h0>0@4$h2$6^i4@2$4@2$4^h7+h0@2$h4+4^hf@2$4^h7+l0>0@3$h7$2\2cp$2@2$a@2$7Z^1@2$ib^1@2$ic+2+i0^he>0@4$d$6^i6@2$4^i3$ha@3$8$3@1$b^he@3$8$3@1$b^hd@3$8$3@1$b^hc@3$8$3@1$b^hb@1$c$3@3$i5$6@hb$h9^k8^k7^k6^k5^k1^k0^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^i9^i8^i7^i6^ha^i4^hb^i3^i2^i1^i0@7$i7@hf$i6^k8^k7^k6^k5^k4^k3^k2^k1^k0^jf^je^jd^jc^jb^ja^j9^j8^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^id^ic^ib^ia^i9@2$id@1$0#k0+mtnu4^i8@1$h5@1$1@1$0#k0^i7@1$i9$6").
Proof.
  intros until csz. intros -> -> ->. intros. unfold PCLASS_SIZE in *.
  eapply combined_hit_spec; eauto.
Qed.

(* [comment removed for export] *)
Definition aframe : ltac2:(zQ "40!jb!le!j4!kie>2sp@1$1@1$0#k0>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2m1$3>2j8@1$2@1$1@1$0#8P") := ltac2:(zQ "e0!ig4!hs1!jb!lsf!le!lsa!j4!ip7!ik7!kie!iqc!iob!ji4!jq9\2sp@1$4@1$2#k0\2ra@1$4@1$2#k0\2s0@1$4@1$2#k0\2s1@1$4@1$2#k0\2s2@1$4@1$2#k0\2s3@1$4@1$2#k0\2s4@1$4@1$2#k0\2s5@1$4@1$2#k0\2s6@1$4@1$2#k0\2s7@1$4@1$2#k0\2s8@1$4@1$2#k0\2s9@1$4@1$2#k0\3s10@1$4@1$2#k0\3s11@1$4@1$2#k0\2m1$9\2j8@1$6@1$4@1$2#8@4$b$8^2@2$c@2$d@1$2#k0^h0-o0@3$1$0@2$aN8^1@3$1$0@1$3@1$5+1@3$1$0@1$3@1$5+h0@3$1$0@1$3^3@3$1$0@1$3^4@3$1$0@1$3^5@3$1$0@1$3^6@3$1$0@1$3^7@3$1$0@1$3^8@3$1$0@1$3^9@3$1$0@1$3^a@3$1$0@1$3^b@3$1$0@1$3^c@3$1$0@1$3^d@3$1$0@1$3^e@3$1$0@1$3^f@1$7$0").

End HCW3.

