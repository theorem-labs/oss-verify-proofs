(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A), the block pcs, the code table's range (1573 words: headamp's out-of-line slow blocks are four instructions long), module paths; kept_run from proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (role's cfg functions have no twin in headamp; same_io_wvb is HPgSteps'). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropKit.v, with its module paths and module names changed; 348 of its 381 lines of code are new or changed and 96 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW3bPre.v at ce91b850dd33, ported to
   reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan): image B's preheader (its pcs, registers and R-relative cells;
   the cursor stays in s2 and what is left in t4 on both arms, buflen is in s10 at PH and is spilled here, F is in
   s8 and s9 and s9 is reused for the `one` of the trap tests); the cells are five regions whose write windows are
   the three real-frame ranges of the build's write set (RtPgImgB hi_w1); the four complement cells the trap tests
   read are kept as YI08.U_not_off's form; the image facts come from lib/AU/RtPgStepsB.v and the memory lemmas from
   lib/AU/RtPgMemB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the property loop's
   preheader of the build (M01) of LLVMFuzzerTestOneInput 0x8076c, PH 0x80ea0 -> N 0x80fb4 (nprops <> 0) / P
   0x82684 (nprops = 0), pod.h:397-398. Proves no function (kind: segment lemma).

   THE CODE. 0x80ea0 .. 0x80ed8 spill a7 (the top word's offset 0) to R+0x20, a6 (its address pp) to R+0x28, s10
   (buflen) to R+0x18, s8 (F) to R+0x10, &pp->n_ent (pp + 0x4d14, from s6 = 0x5000) to R+0x138 and its shadow index
   to R+0xf8, s9 (F) to R+0x60 and &pp->is_props (pp + 0x4008, from a1 = 0x4000) to R+0x8; 0x80ed4 loads nprops
   (R+0x118) and `bnez` 0x80edc leaves to 0x80ee4 or, through `j` 0x80ee0, to P (where the cursor is still in s2).
   0x80ee4 .. 0x80fb0 set the loop's registers (seen = 0, i = 0, &t, &r, the digit multiplier, s8 = -8, s9 = 1) and
   the cells the property loop reloads (RtPgSegB.rsb_Kc), among them the four complements ~(F+0xa0), ~(pp+0x4014),
   ~(F+0x218) that `not` writes and ~pp that E01 left.

   HOW. The symbolic state is rebuilt from PH's cut over the token engine (no instrumented check runs here, so no
   shadow entry is needed). The R-relative cells are five regions on s1: [R, R+0x30), [R+0x58, R+0x148) and
   [R+0x150, R+0x180) are writable (the three real-frame ranges of the build's write set RtPgImgB.hi_w1, inside the
   segment's stack window), [R+0x30, R+0x58) and [R+0x148, R+0x150) are read only. The cells the preheader keeps
   (the four header values, fl, mask, nprops, the shape-7 flag, ~pp and -0x3ffd) are their chunks, over the extra
   atoms 32 .. 41. a7 = 0, a1 = 0x4000 and s6 = 0x5000 are pinned, and the one atom bound the state carries (s1's)
   is a closed numeral. The engine stops at `bnez a0` 0x80edc (a0 = nprops); the taken arm runs to N, the other to
   P. Every fact of the end cut is read from the final symbolic state: a register from its symbolic value, a cell
   from its chunk. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YI00 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Definition W3BP_PH : Z := 0x80ea0.
Definition W3BP_N : Z := 0x80fb4.
Definition W3BP_P : Z := 0x82684.
(* the 70 instruction words 0x80ea0 .. 0x80fb4 *)
Definition w3bp_tbl : ctable := build_table rsegs W3BP_PH 70 TEmpty.
Lemma w3bp_tbl_ok : table_ok rsegs w3bp_tbl.
Proof. apply build_table_ok0. unfold W3BP_PH. lia. Qed.
Definition w3bp_Bx : sv := SOff 20 0.
Definition w3bp_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition W3BP_RLO : Z := 0x7fff7f800000.
Definition W3BP_RHI : Z := 2 ^ 47.
Definition W3BP_M3FFD : Z := 0xffffffffffffc003.   (* -0x3ffd mod 2^64 *)

(* the three real-frame ranges the preheader may write (RtPgImgB hi_w1's R-relative ranges) *)
Definition w3bp_Z (R a : Z) : Prop :=
(R <= a < R + 0x30) \/ (R + 0x58 <= a < R + 0x148) \/ (R + 0x150 <= a < R + 0x180).

(* a7 = 0, a1 = 0x4000 and s6 = 0x5000 are pinned *)
Definition w3bp_regs_ph : list sv :=
sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 17) (SLit 0)) (Z_to_bv 5 11) (SLit 0x4000))
  (Z_to_bv 5 22) (SLit 0x5000).
Definition w3bp_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x0 0x30 0x0 0x30 [].
Definition w3bp_rB : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x30 0x58 0 0
[YP09.mkChunk 0x30 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 34 0));
 YP09.mkChunk 0x40 (CVal 8 (SOff 35 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 32 0));
 YP09.mkChunk 0x50 (CVal 8 (SOff 36 0))].
Definition w3bp_rC : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x58 0x148 0x58 0x148
[YP09.mkChunk 0x108 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x110 (CVal 8 (SOff 39 0));
 YP09.mkChunk 0x118 (CVal 8 (SOff 40 0)); YP09.mkChunk 0x120 (CVal 8 (SLit W3BP_M3FFD))].
Definition w3bp_rD : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x148 0x150 0 0 [YP09.mkChunk 0x148 (CVal 8 (SOff 37 0))].
Definition w3bp_rE : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x150 0x180 0x150 0x180
[YP09.mkChunk 0x158 (CVal 8 (SOff 16 16384)); YP09.mkChunk 0x168 (CVal 8 (SOff 16 0));
 YP09.mkChunk 0x170 (CVal 8 (SOff 41 0))].
(* the one atom bound the state carries, a closed numeral *)
Definition w3bp_atoms : list (nat * afact) := [(9%nat, mkAF W3BP_RLO W3BP_RHI 0)].
Definition w3bp_ss : sstate :=
mkSS W3BP_PH w3bp_regs_ph [w3bp_rA; w3bp_rB; w3bp_rC; w3bp_rD; w3bp_rE] None (mkFacts w3bp_atoms [] []).

(* the ten values of PH's cells, as the extra atoms 32 .. 41 *)
Definition w3bp_extra (e : rt_renv) (sh np : Z) : list word :=
[Z_to_bv 64 (q_b3 e); Z_to_bv 64 (Z.shiftl (q_b6 e) 8); Z_to_bv 64 (q_b5 e);
 Z_to_bv 64 (Z.shiftl (q_b4 e) 8); Z_to_bv 64 (q_fl e); Z_to_bv 64 (q_mask e);
 Z_to_bv 64 (Z.lnot (q_pp e)); Z_to_bv 64 (Z.b2z (sh =? 7)); Z_to_bv 64 np;
 Z_to_bv 64 (shadow_addr (q_pp e + 0x4000))].

(* the complement of an address, as the cells hold it *)
Lemma w3bp_lnot : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof.
intros p Hp. replace (Z.lnot p) with ((2 ^ 64 - 1 - p) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* the block's image has its full size at every shape *)
Lemma w3bp_len_pc0 : forall sh, 0 <= sh < 8 -> length (pc_image (PbCut sh [] None)) = 19744%nat.
Proof.
intros sh Hsh. assert (H8 : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
destruct H8 as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a register the final symbolic state still holds as its own atom keeps its value *)
Lemma w3bp_reg_kept : forall E ss ms regs0 extra (H : word -> bool) (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> (forall n, (n < 32)%nat -> ew E n = ew (Ereg regs0 extra) n) ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H r HS HA Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
pose proof (u5_range r) as Hr. rewrite HA by lia. apply ew_Ereg_reg.
Qed.

(* a run keeps every byte outside the zone its write windows lie in *)
Lemma w3bp_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* the value of a symbolic expression of a final state, from the exact values of its atoms (U facts in context) *)
Ltac w3bp_den :=
  rewrite denot_lit_U; apply Z_to_bv64_eq_mod;
  repeat match goal with H : U ?E ?x = _ |- context [U ?E ?x] => rewrite H end;
  rewrite ?U_SAlu, ?U_SOff, ?U_SLit; cbn [zalu_raw];
  repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite H end;
  rewrite ?Z.add_0_r; try unfold zcanon; try unfold M64; rewrite ?Zmod_mod;
  first [reflexivity | f_equal; lia | lia].
(* the machine state a final symbolic state describes *)
Ltac w3bp_ms HS := lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => m end.
(* one (location, value) fact of a cut, read from the final symbolic state HS: a register from its symbolic value,
   a cell from the chunk at that offset of one of the regions *)
Ltac w3bp_fact HS E :=
  let ms := w3bp_ms HS in
  cbn [fst snd rt_at rt_xv];
  first
  [ lazymatch goal with
    | |- getr _ ?r = _ =>
        rewrite (st_ok_restrict_reg rsegs _ E _ ms r HS);
        lazymatch goal with |- sv_denot _ (sr_get ?l ?r') = _ =>
          let x := eval vm_compute in (sr_get l r') in change (sr_get l r') with x end;
        unfold w64; w3bp_den
    end
  | match goal with
    | C : YP09.chunk_ok _ _ _ ?R (YP09.mkChunk ?o (CVal 8 ?ex)) |- _ =>
        apply (val_of_chunk_ok rsegs E _ R o 8 ex _ C);
        [ w3bp_den
        | split; [apply Z.mod_pos_bound; cbv; reflexivity
                 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; cbv; reflexivity]
        | cbv; discriminate ]
    end ].
Ltac w3bp_split_chunks Cs :=
  repeat lazymatch type of Cs with _ /\ _ => let c := fresh "Cn" in destruct Cs as [c Cs] end.
Ltac w3bp_kio := first [apply same_io_refl | eapply same_io_trans; [| apply RtPgStepsB.same_io_wvb]; w3bp_kio].
(* the run's writes are the segment's stack window: each writable region on atom 9, R = sp0 + (R - sp0); the
   read-only ones write nothing *)
Ltac w3bp_awr U9 R sp :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp' ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp' fp b0 bc ly0 own0) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp));
        [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ].
(* ... and those bytes are in w3bp_Z *)
Ltac w3bp_kw U9 :=
  let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (rg & Hr & Hb); unfold w3bp_Z;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hr end;
  repeat (destruct Hr as [<-|Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite U9 in Hb; lia |]);
  destruct Hr.
(* fold a run's frame into the kept-bytes fact KE (every byte outside w3bp_Z R as at PH) *)
Ltac w3bp_keep KE U9 R :=
  lazymatch goal with HFr : frame_of ?E0 ?rs (mrestrict _ _) (mrestrict _ _) |- _ =>
    let KW := fresh "KW" in let KE' := fresh "KE" in
    assert (KW : forall a, in_wrange E0 rs a -> w3bp_Z R a) by w3bp_kw U9;
    pose proof (w3bp_kept_run (w3bp_Z R) _ _ _ _ _ _ KE HFr KW) as KE';
    clear KE KW HFr; rename KE' into KE end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the final regions' chunks, one hypothesis each *)
Ltac w3bp_chunks HS U9 :=
  let HOK := fresh "HOK" in
  pose proof (st_ok_mem_ok rsegs _ _ _ HS) as (_ & HOK & _); cbn [ss_mem] in HOK;
  repeat (lazymatch type of HOK with
    | Forall _ (_ :: _) =>
        let Cs := fresh "Cs" in
        pose proof (Forall_inv HOK) as (_ & _ & _ & Cs); apply Forall_inv_tail in HOK;
        cbn [YP09.r_base YP09.r_chunks base_val] in Cs; rewrite U9 in Cs;
        repeat rewrite Forall_cons_iff in Cs; w3bp_split_chunks Cs
    end);
  clear HOK.
(* rsb_core at the end: the journal, s1 .. s3 as at the start (their own atoms), the frames, blocks, I/O and meter,
   and every byte outside the segment's write set as at the start (the run wrote only w3bp_Z R, which is three of
   hi_w1's real-frame ranges) *)
Ltac w3bp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE :=
  let ms := w3bp_ms HS in
  unfold rsb_core, rsb_mid; split; [exact HJ|];
  split; [let rr := fresh "rr" in let Hrr := fresh "Hrr" in
          intros rr Hrr; rewrite <- (H234 rr Hrr); destruct Hrr as [->|[->| ->]];
          (eapply (w3bp_reg_kept E _ ms regs2 _ (w_H W2)); [exact HS | exact HAE | vm_compute; reflexivity]) |];
  split; [exact Hfr|]; split; [exact Hperm|];
  split; [eapply same_io_trans; [exact Hio | w3bp_kio] |];
  split; [exact Hmo|];
  let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let HnE := fresh "HnE" in
  let X := fresh "X" in
  intros a Ha HnS HnE; rewrite <- (Hkeep a Ha HnS HnE); apply KE; [exact Ha|];
  intros X; apply HnE; unfold rsb_E1; left; unfold rt_inw; cbn [hi_w1 rate_himg_B];
  unfold w3bp_Z in X; destruct X as [X|[X|X]];
  [ apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
  | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
  | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd ];
  cbn [fst snd rt_xv]; lia.
(* the frame's shadow bytes: below the stack, so outside w3bp_Z R *)
Ltac w3bp_fsh HS HFSH KE W2 mem2 :=
  let ms := w3bp_ms HS in
  let i := fresh "i" in let Hi := fresh "Hi" in let X := fresh "X" in
  apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ rsb_P0 HFSH);
  intros i Hi; change (length rsb_P0) with 88%nat in Hi;
  apply KE; [unfold shadow_addr, SHADOW_OFF; lia | intros X; unfold w3bp_Z, shadow_addr, SHADOW_OFF in X; lia].
(* the block's bytes: below the stack too *)
Ltac w3bp_pp HS HPP KE W2 mem2 Lpc :=
  let ms := w3bp_ms HS in
  let y := fresh "y" in let Hy := fresh "Hy" in let X := fresh "X" in
  apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) _ _ HPP);
  rewrite Lpc; change (Z.of_nat 19744) with 19744;
  intros y Hy; apply KE; [lia | intros X; unfold w3bp_Z in X; lia].

(* PH -> N | P *)
Lemma rsb_piece_W3b_pre : rsb_piece_W3b_pre_stmt rsegs B MT.
Proof.
intros cx POST rest HST HN HP ly2 S2 W2 regs2 mem2 md2 r sh np HC.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof RtPgStepsB.rtsb_wx as Hwx. pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
destruct HST as (HPRE & _ & _ & Hlen & _).
pose proof HPRE as (HJc & _ & _ & _ & _ & HSe & _ & HRsz & HRstk & Hown & HFe & _ & Hppc & _ & _ & _ & _ & _ & _ & _
  & Hfresh & _ & _).
cbn [hi_rsz hi_cid rate_himg_B] in HRsz, Hown, HFe.
destruct HC as (HCORE & HAT & HFSH & HPP & HIN & HSUF & Esh & Enp & Er).
pose proof HCORE as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (HT : T_SEG_STK = 16384) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hppc) as (_ & Hpp0 & Hppcl & Happ & _ & _).
change (req_size PP_SIZE) with 19744 in Hppcl, Happ.
assert (HFin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx)))
  by (rewrite Hfrsc; apply in_or_app; left; exact Hown).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HARc HFin) as (HF0 & HFc & _).
rewrite <- HFe in HF0, HFc. change (fs_frame_bytes 4) with 1024 in HFc.
assert (Hnp : 0 <= np <= 3)
  by (assert (0 <= np < 4) by (rewrite Enp; unfold rsb_np; apply Z.mod_pos_bound; lia); lia).
assert (Hsh8 : 0 <= sh < 8) by (rewrite Esh; unfold rsb_sh; apply Z.mod_pos_bound; lia).
assert (HFd : 0 <= q_F (x_e rsegs cx) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply (Z.div_le_mono _ 0x7fffff800000 8); lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (w3bp_len_pc0 sh Hsh8) as Lpc.
(* the cursor and the bytes left are in range *)
assert (Hcur : 0 <= rsb_cur rsegs cx rest r < 2 ^ 64 /\ 0 <= Z.of_nat (length r) < 2 ^ 64).
{ pose proof HIN as (Hleft & _ & _ & _ & _ & Hsrc0 & Hsrc1 & _).
  pose proof HSUF as (j & Hj & Hrj). unfold rsb_cur. rewrite Hrj, length_skipn. lia. }
(* the bounds every later `lia` needs, as plain inequalities; then the structural facts go, so that each `lia`
   below sees a small context (with them in it, the 150 calls of this proof took over 15 minutes) *)
assert (HR0 : 0x7fff7f800000 + 16384 <= q_R (x_e rsegs cx)) by lia.
assert (HR1 : q_R (x_e rsegs cx) + 0x220 <= x_sp0 rsegs cx) by lia.
assert (HR2 : x_sp0 rsegs cx - x_STK rsegs cx <= q_R (x_e rsegs cx) - 16384) by lia.
assert (HR3 : x_sp0 rsegs cx <= 2 ^ 47) by lia.
assert (HppR : q_pp (x_e rsegs cx) + 19744 <= q_R (x_e rsegs cx) - 16384) by lia.
assert (HPlo : 4096 <= q_pp (x_e rsegs cx)) by lia.
assert (HFlo : 4096 <= q_F (x_e rsegs cx)) by lia.
assert (HFhi : q_F (x_e rsegs cx) + 1024 <= 0x7fffff800000) by lia.
clear - LAWS Hwx Hsegs HJ H234 Hfr Hperm Hio Hmo Hkeep HFSH HPP HIN HSUF Esh Enp Er Hlen Hstkp HAT HN HP Hnp Hsh8
  HFd Lpc Hcur HR0 HR1 HR2 HR3 HppR HPlo HFlo HFhi HSe.
(* PH's facts *)
unfold rsb_at_cx, rsb_at, rsb_L_PH, rsb_Hch, rsb_cur2 in HAT. cbn [app] in HAT.
repeat rewrite Forall_cons_iff in HAT.
destruct HAT as (A16 & A17 & A22 & A8 & A9 & A19 & A20 & C158 & A24 & A25 & C168 & C50 & C118 & C110 & C170 & C120
  & A11 & C108 & C48 & C30 & C38 & C40 & A26 & C148 & A18 & A29 & _).
cbn [fst snd rt_at rt_xv] in A16, A17, A22, A8, A9, A19, A20, C158, A24, A25, C168, C50, C118, C110, C170, C120,
  A11, C108, C48, C30, C38, C40, A26, C148, A18, A29.
remember (Ereg regs2 (w3bp_extra (x_e rsegs cx) sh np)) as E eqn:HE.
assert (HAE : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 (w3bp_extra (x_e rsegs cx) sh np)) n)
  by (intros; subst E; reflexivity).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; subst E; exact (ew_Ereg_nat regs2 _ n rr Hn)).
assert (Ux : forall n v, (n < 32)%nat -> getr regs2 (Z_to_bv 5 (Z.of_nat n)) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n v Hn Hg Hv. rewrite (EE n (Z_to_bv 5 (Z.of_nat n))), Hg by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 5) with 32; rewrite Z.mod_small; lia). apply unsigned_lit_small. exact Hv. }
assert (Uex : forall j v, nth j (w3bp_extra (x_e rsegs cx) sh np) (Z_to_bv 64 0) = Z_to_bv 64 v ->
  bv_unsigned (ew E (32 + j)%nat) = v mod 2 ^ 64).
{ intros j v Hj. subst E. rewrite (ew_Ereg_extra regs2 _ j), Hj. apply Z_to_bv_unsigned. }
assert (U8 : bv_unsigned (ew E 8) = q_S (x_e rsegs cx)) by (apply (Ux 8%nat); [lia | exact A8 | lia]).
assert (U9 : bv_unsigned (ew E 9) = q_R (x_e rsegs cx)) by (apply (Ux 9%nat); [lia | exact A9 | lia]).
assert (U16 : bv_unsigned (ew E 16) = q_pp (x_e rsegs cx)) by (apply (Ux 16%nat); [lia | exact A16 | lia]).
assert (U18 : bv_unsigned (ew E 18) = rsb_cur rsegs cx rest r) by (apply (Ux 18%nat); [lia | exact A18 | lia]).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr (q_F (x_e rsegs cx)))
  by (apply (Ux 19%nat); [lia | exact A19 | unfold shadow_addr, SHADOW_OFF; lia]).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (apply (Ux 20%nat); [lia | exact A20 | unfold SHADOW_OFF; lia]).
assert (U24 : bv_unsigned (ew E 24) = q_F (x_e rsegs cx)) by (apply (Ux 24%nat); [lia | exact A24 | lia]).
assert (U25 : bv_unsigned (ew E 25) = q_F (x_e rsegs cx)) by (apply (Ux 25%nat); [lia | exact A25 | lia]).
assert (U26 : bv_unsigned (ew E 26) = q_buflen (x_e rsegs cx) mod 2 ^ 64).
{ rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), A26. unfold w64. apply Z_to_bv_unsigned. }
assert (U29 : bv_unsigned (ew E 29) = Z.of_nat (length r)) by (apply (Ux 29%nat); [lia | exact A29 | lia]).
assert (U32 : bv_unsigned (ew E 32) = q_b3 (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 0%nat _ eq_refl).
assert (U33 : bv_unsigned (ew E 33) = Z.shiftl (q_b6 (x_e rsegs cx)) 8 mod 2 ^ 64) by exact (Uex 1%nat _ eq_refl).
assert (U34 : bv_unsigned (ew E 34) = q_b5 (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 2%nat _ eq_refl).
assert (U35 : bv_unsigned (ew E 35) = Z.shiftl (q_b4 (x_e rsegs cx)) 8 mod 2 ^ 64) by exact (Uex 3%nat _ eq_refl).
assert (U36 : bv_unsigned (ew E 36) = q_fl (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 4%nat _ eq_refl).
assert (U37 : bv_unsigned (ew E 37) = q_mask (x_e rsegs cx) mod 2 ^ 64) by exact (Uex 5%nat _ eq_refl).
assert (U38 : bv_unsigned (ew E 38) = Z.lnot (q_pp (x_e rsegs cx)) mod 2 ^ 64) by exact (Uex 6%nat _ eq_refl).
assert (U39 : bv_unsigned (ew E 39) = Z.b2z (sh =? 7) mod 2 ^ 64) by exact (Uex 7%nat _ eq_refl).
assert (U40 : bv_unsigned (ew E 40) = np mod 2 ^ 64) by exact (Uex 8%nat _ eq_refl).
assert (U41 : bv_unsigned (ew E 41) = shadow_addr (q_pp (x_e rsegs cx) + 0x4000) mod 2 ^ 64)
  by exact (Uex 9%nat _ eq_refl).
clear Uex.
(* the two shapes the engine leaves in the cells: the shadow index of &pp->n_ent and the four complements *)
assert (HU68 : U E (SAlu ALU_SRL (SOff 16 19732) (SLit 3)) = Z.shiftr (q_pp (x_e rsegs cx) + 0x4d14) 3).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U16.
  change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
  rewrite (Z.mod_small (q_pp (x_e rsegs cx) + 19732)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8. apply Z.mod_small. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
assert (HUd8 : U E (SAlu ALU_XOR (SOff 25 160) (SLit (-1))) = Z.lnot (q_F (x_e rsegs cx) + 160) mod 2 ^ 64).
{ rewrite (w3bp_lnot (q_F (x_e rsegs cx) + 160)) by lia.
  apply (U_not_off E 25%nat (q_F (x_e rsegs cx)) 160);
    [rewrite <- U25; symmetry; apply Z_to_bv_bv_unsigned | lia | lia]. }
assert (HU100 : U E (SAlu ALU_XOR (SOff 25 536) (SLit (-1))) = Z.lnot (q_F (x_e rsegs cx) + 536) mod 2 ^ 64).
{ rewrite (w3bp_lnot (q_F (x_e rsegs cx) + 536)) by lia.
  apply (U_not_off E 25%nat (q_F (x_e rsegs cx)) 536);
    [rewrite <- U25; symmetry; apply Z_to_bv_bv_unsigned | lia | lia]. }
assert (HUf0 : U E (SAlu ALU_XOR (SOff 16 16404) (SLit (-1))) = Z.lnot (q_pp (x_e rsegs cx) + 16404) mod 2 ^ 64).
{ rewrite (w3bp_lnot (q_pp (x_e rsegs cx) + 16404)) by lia.
  apply (U_not_off E 16%nat (q_pp (x_e rsegs cx)) 16404);
    [rewrite <- U16; symmetry; apply Z_to_bv_bv_unsigned | lia | lia]. }
(* the symbolic state at PH *)
assert (HS : st_ok rsegs E w3bp_ss (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 W3BP_PH) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold w3bp_ss. apply (entry_st_ok_full rsegs).
  - unfold w3bp_regs_ph.
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |]
      | reflexivity |] | reflexivity |].
    + rewrite A17. reflexivity.
    + rewrite A11. reflexivity.
    + rewrite A22. reflexivity.
  - vm_compute. reflexivity.
  - rewrite <- HE. unfold w3bp_rA, w3bp_rB, w3bp_rC, w3bp_rD, w3bp_rE.
    repeat apply Forall_cons; try apply Forall_nil;
    (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
     rewrite U9; split; [lia|]; split; [lia|];
     split; [intros o Ho; first [lia | apply (apresent_writable rsegs); apply Hstkp; lia]|];
     repeat apply Forall_cons; try apply Forall_nil;
     match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 ?ex)) =>
       lazymatch goal with C : val_mem _ _ (_ + o) 8 ?v |- _ =>
         apply (chunk_ok_val rsegs E _ _ o 8 ex v);
         [ w3bp_den
         | split; [apply Z.mod_pos_bound; lia
                  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia]
         | cbn; lia | exact C ] end end).
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val w3bp_rA w3bp_rB w3bp_rC w3bp_rD w3bp_rE]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms w3bp_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold W3BP_RLO, W3BP_RHI. repeat split; lia. }
assert (SHOK : sh_ok rsegs w3bp_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w3bp_Z (q_R (x_e rsegs cx)) a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem2 a) by (intros; reflexivity).
clear HE.
clear - LAWS Hwx Hsegs HJ H234 Hfr Hperm Hio Hmo Hkeep HFSH HPP HIN HSUF Esh Enp Er Hlen Hstkp HN HP Hnp Hsh8 HFd
  Lpc Hcur HR0 HR1 HR2 HR3 HppR HPlo HFlo HFhi HSe HS SHOK KE HAE U8 U9 U16 U18 U19 U20 U24 U25 U26 U29 U32 U33 U34
  U35 U36 U37 U38 U39 U40 U41 HU68 HUd8 HU100 HUf0.
unfold cfg_at. change (w64 RSB_PH) with (Z_to_bv 64 W3BP_PH).
(* 0x80ea0 .. 0x80ed8: the eight spills; stop at `bnez a0` 0x80edc *)
aj_run_to_tok w3bp_tbl_ok HS HJ SHOK w3bp_Bspan W3BP_N.
{ w3bp_awr U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
w3bp_keep KE U9 (q_R (x_e rsegs cx)).
srr_branch_tok w3bp_tbl_ok HS SHOK w3bp_Bspan.
- (* nprops <> 0: 0x80ee4 .. 0x80fb0, the loop's registers and cells, to N *)
  rewrite branch_ne_U, U_SOff, U_SLit, U40, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok w3bp_tbl_ok HS HJ SHOK w3bp_Bspan W3BP_N.
  { w3bp_awr U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3bp_keep KE U9 (q_R (x_e rsegs cx)).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HN ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r eq_refl) end.
  unfold rsb_cut_N. split; [w3bp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE|].
  split.
  { (* the chunks stay inside this goal: every other goal's `lia` would walk them *)
    w3bp_chunks HS U9.
    unfold rsb_at_cx, rsb_at, rsb_L_N, rsb_Rc, rsb_Rc0, rsb_Kc, rsb_Hc, rsb_cur2, rsb_seen. cbn [app existsb Z.b2z].
    repeat apply Forall_cons; try apply Forall_nil; w3bp_fact HS E. }
  split; [w3bp_fsh HS HFSH KE W2 mem2|].
  split; [w3bp_pp HS HPP KE W2 mem2 Lpc|].
  split; [exact HIN|]. split; [exact HSUF|].
  split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
  split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|]. split; [lia|].
  rewrite Er. reflexivity.
- (* nprops = 0: `j` 0x80ee0 to P *)
  rewrite branch_ne_U, U_SOff, U_SLit, U40, Z.add_0_r in Hc. unfold zcanon, M64 in Hc.
  rewrite Zmod_mod, (Z.mod_small np), Z.mod_0_l in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok w3bp_tbl_ok HS HJ SHOK w3bp_Bspan W3BP_P.
  { w3bp_awr U9 (q_R (x_e rsegs cx)) (x_sp0 rsegs cx). }
  w3bp_keep KE U9 (q_R (x_e rsegs cx)).
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ m HS eq_refl) at 1;
    apply (HP ly2 S2 W2 (ms_regs m) (ms_mem m) _ sh np [] r) end.
  unfold rsb_cut_P, rsb_Pbody. split; [split|].
  + w3bp_core HS E HAE regs2 W2 HJ H234 Hfr Hperm Hio Hmo Hkeep KE.
  + split; [w3bp_fsh HS HFSH KE W2 mem2|].
    split; [w3bp_pp HS HPP KE W2 mem2 Lpc|].
    split; [exact HIN|]. split; [exact HSUF|].
    split; [split; [exact Hsh8|]; split; [constructor|]; split; [cbn; constructor | cbn; lia]|].
    split; [exact Hlen|]. split; [exact Esh|]. split; [exact Enp|]. split; [cbn; lia|].
    rewrite Er. reflexivity.
  + w3bp_chunks HS U9.
    unfold rsb_at_cx, rsb_at, rsb_L_P, rsb_Hc. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; w3bp_fact HS E.
Qed.
End d.
End b.

Print Assumptions rsb_piece_W3b_pre.
