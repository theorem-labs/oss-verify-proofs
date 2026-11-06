(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge Frame TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3andhc2eq46Stdlib6ZArith6BinInt1Zjb4landjb2lejb2ltjb6modulojb3powjb3sub04Npos35stdpp9bitvectorbdefinitionsnf2bv37Corelib4Init9Datatypesq14listq16option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~s94cellq14Someq14cons3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehha7Segments92C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hlf3mrdhlf2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hq68rw_cellsq14prodq13fstq13sndhc2or37Corelib5Lists7ListDefig56Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ii68AIMG_TOP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~imd6AHI_LOimd9ALOWSH_LOimd7AAPP_HIimd2sh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6AsWalk~~~~~~it37wins_hi79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jha7outsidejhaddisjoint_fromjb3addimdaaccessibleimd3memjha3ivljha5munchimdbaddressableii65asegsjha5wmonoimd5shvisq13nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjsddov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kh52b8jb3divjb3muljb6shiftrnf7Z_to_bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.

Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in nonneg_lit d
      | X => let c1 := zlit c1 in nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in nonneg_lit d
      end
  end.

Lemma land_align32 : ltac2:(zQ "90!h9!j0!j6!l3!la!lf!m4!md!n3>1x$0>0@2$1@2$4Z^1@2$5^1@2$7+2+k0@3$2$0@2$3^2+vvvvvvvvvvvvvvu0@2$8^2@2$6^2+i0").
Proof.
  intros x Hx. transitivity (Z.ldiff (Z.land x (Z.ones 64)) (Z.ones 5)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.

Lemma land_7 : ltac2:(zQ "40!h9!j6!l3!m4>1y$0@3$1$0@2$2^1+7@2$3^1+8").
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_C1_mrd : ltac2:(zQ "e0!n9!pc!r9!s0!hg5!hgc!hh3!j6!h9!hkf!hla!hp9!hq0!hu1>4segs@1$2$9>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a$8>1b@1$1@1$0#8>2cs@1$2$4>0@4$d^5^4^3@3$6$4@1$a^2^1@3$7@1$3@1$1@1$0#8@3$b^6^5@1$c^4@2$5@1$1@1$0#8^3").
Proof.
  intros segs m a b cs [[WF (B0 & B1 & BB)] _]. specialize (BB 0%nat ltac:(cbn; lia)). cbn in BB.
  rewrite Z.add_0_r in BB. exact BB.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wins_hi : ltac2:(zQ "30!h9!r9!hud>1W@1$1@2$2$0$0P") := ltac2:(zQ "c0!h9!hud!la!hv4!r9!hva!j0!ig0!ihc!im1!iqb!ir5\1W@1$4@2$1$0$0@3$8@2$1$0$0\2iv@2$1$0$0@2$7@2$6@2$2$9@3$3$0$0^1@2$2@3$5$0$0^1$b@2$2$a@3$3$0$0^1^1").

Lemma wins_hi_outside : ltac2:(zQ "a0!h9!r9!hud!j0!is2!isd!jgf!jl6!la!lf>1W@1$1@2$2$0$0>1x$0>0@1$6^2>0@2$3@2$8Z^2@2$9^2$4@2$7^4@1$5^3").
Proof.
  induction W as [|[lo hi] W IH]; intros x HW Hx; cbn; [exact I|].
  inversion HW; subst. cbn in *. pose proof (sh_below_app x Hx).
  assert (ALOWSH_LO < sh x) by (unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; lia).
  split; [lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma wins_hi_disjoint : ltac2:(zQ "a0!h9!la!r9!hud!j0!iqb!ir5!jgf!jm1!jn2>1W@1$2@2$3$0$0>1a$0>1n$0>0@1$7^3>0@2$4@2$1$6^3@2$1@2$9^3^2$5@3$8^5^4^3").
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW [Ha Hn]; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia| apply IH; [assumption| split; assumption]].
Qed.

Lemma sh_ge_lowsh : ltac2:(zQ "40!la!h9!ir5!isd>1a$1>0@2$0Z^1@2$0$2@1$3^2").
Proof. intros a Ha. unfold sh, ALOWSH_LO. rewrite ASHADOW_BASE_val. lia. Qed.

Lemma accessible_transport_hi : ltac2:(zQ "a0!n9!h9!jn8!pc!r9!s0!jo6!jgf!jod!jp4>1W@1$4$8>1m$6>2m'>0@1$3@1$0#k0@1$5@1$3@1$0#8>1a$1>1n$1>0@3$2^4^2^1>0@3$9^6^5^4>0@1$7^7@3$2^6^5^4").
Proof.
  intros W m m' a n AC MU HW. eapply accessible_transport; [exact AC| exact MU|].
  ndestruct AC as (A0 & A1 & _). intros x Hx. apply wins_hi_outside; [exact HW| lia].
Qed.

Lemma addressable_transport_hi : ltac2:(zQ "f0!n9!h9!jpd!pc!r9!s0!jqc!is2!jo6!jgf!jod!jp4!jr5!jn2!la>1W@1$4$a>1m$8>2m'>0@1$3@1$0#k0@1$5@1$3@1$0#8>1A$1>1n$1>0@3$2^4^2^1>0@3$b^6^5^4>0@3$c$6^6^5>0@2$e@2$d^5^4$7>0@1$9^9@3$2^8^7^6").
Proof.
  intros W m m' A n AD MU WM Htop HW. eapply addressable_transport; [exact AD| exact MU| exact WM|].
  ndestruct AD as (Hn & A0 & A8 & _). apply wins_hi_disjoint; [exact HW|]. split; [apply sh_ge_lowsh; lia| apply sh_nsh_high; lia].
Qed.

Lemma shvis_transport_hi : ltac2:(zQ "f0!la!n9!h9!jre!pc!r9!s0!j0!jqc!is2!jo6!jgf!jod!jp4!jr5>1W@1$5$c>1m$a>2m'>0@1$4@1$1#k0@1$6@1$4@1$1#8>2lo$2>2hi$2>0@3$3^4^2^1>0@3$d^6^5^4>0@3$e$8^6^5>0@2$7@2$0Z^5@2$0^5^4>0@2$0^5$9>0@1$b^a@3$3^9^8^7").
Proof.
  intros W m m' lo hi SV MU WM H0 Htop HW. eapply shvis_transport; [exact SV| exact MU| exact WM|].
  npose (hull_lo_le lo ltac:(lia)) as (L1 & L2 & L3).
  apply wins_hi_disjoint; [exact HW|]. split; [apply sh_ge_lowsh; lia|]. npose (hull_hi_ge hi ltac:(lia)) as (G1 & G2 & G3).
  assert (LE : hull_hi hi <= AAPP_HI) by (unfold AAPP_HI in *; Z.div_mod_to_equations; nia).
  pose proof (sh_mono _ _ LE) as K. unfold sh, AAPP_HI, AHI_LO in *. rewrite ASHADOW_BASE_val in *.
  change (2147450880 + 2^47 / 8) with 17594333495296 in K. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma addressable_rd : ltac2:(zQ "h40!n9!h9!pc!jn2!la!r9!hgc!hh3!js7!s0!j6!kg4!jqc!jpd!jo6!kl0!kl6!klc!km2!kmb>1m$e>1A$1>1n$1>1a$1>1w$1>0@3$d^5^4^3>0@2$4^5^3>0@2$4+1^3>0@2$4@2$3^5^4@2$3^7@2$h1+8@2$h0^6+8@3$a@1$9@1$5@1$2@1$0#8@4$b$c^9@2$h3@1$0#k0@2$3@2$h2^6+3+nvvvogg0N1@2$6@1$5@1$2@1$0#8@3$7@1$2@1$0#8@1$fZ@1$8@1$2@1$0#8").
Proof.
  intros m A n a w T Ha Hw Hhi. pose proof T as [Hn0 (P0 & _ & _)].
  apply (addressable_read0_w m A n a w); [exact T| lia| exact Hw| exact Hhi|].
  rewrite <- sh_shiftr by lia. rewrite ASHADOW_BASE_val. reflexivity.
Qed.
(* [comment removed for export] *)
