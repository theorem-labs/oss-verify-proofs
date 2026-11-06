(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v; 435 of its 506 lines of code are new or changed and 675 lines of the source are left out. *)
(* Case 3 of the B walk of LLVMFuzzerTestOneInput, segment B: from the point C3_RN (0x80828, read_name has returned)
   to the point C3_SN (0x80850, reac_boxreg_set_name has returned); BoxBLxCase3Defs.v holds the points.
   The code (offsets from 0x7ffac in the listing):
   - 0x80828 .. 0x80848: s3 = name (a0), s9 = op & 8, a2 = ((s9 >> 3) - 1) & name = op & 8 ? NULL : name,
     s7 = (int8) idx (slli / srai 0x38 of s8), a0 = r (s4), a1 = s7; registers only, so the engine runs it on a
     state with no region (c3B_seat) and stops at the call;
   - 0x8084c: reac_boxreg_set_name (r, (int8) idx, op & 8 ? NULL : name), lx_hyps' lh_set_name (BoxBReacBoxregSetName.v),
     whose post is FP-existential (apost_baseF: it returns at SOME fx' with lx_fxr fx fx'), so c3B_call binds the call
     with SRr_bind and lands on C3_SN taken at fx'; the caller's journal across
     the call comes from afn_pre_at / ajournal_sub_tok: the registry block is the call's footprint and none of the
     caller's blocks;
     the name's premises are BoxBLxCase3Defs.v c3_name_ok (op & 8 = 0) or NULL with ""; the image's "%s" and ""
     (A_OBJ 10 / 11) come from BLxLib (their read-only bytes, margins, and their shadow from the const law's cells:
     c3B_globs); the call chain is lx_achain at sp1 (c3B_achain);
   - the return lands on 0x80850 = C3_SN: set_name's post gives the registry's new bytes, its journal keeps every
     other byte the cut speaks about (BoxBLxSeat.v lx_keep_call_fp with the name block, c3B_fp), and the
     callee-saved registers keep s3, s7, s8, s9 and the loop's registers. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReadName BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase3Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd printf_facts_c read_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.

Lemma c3B_ms_eq : forall pc (ms : machine_state),
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros pc ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
  destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
  subst. reflexivity.
Qed.

Lemma c3B_seat : forall (W3 : world SEGS) (regs : bvmap 5 word) m pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
  intros W3 regs m pc. rewrite restrict_mkst_fx.
  apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | apply Forall_nil | exact I | exact (conj I (conj I I))].
Qed.

Definition C3B_SB : Z := 0x7fff8000.
Definition C3B_Bx : sv := SLit C3B_SB.
Definition C3B_span : Z * Z := (C3B_SB, C3B_SB + 2 ^ 44 - 1).

Lemma c3B_w64_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = w64 z.
Proof.
  intros z. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.

Lemma c3B_U_atom : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
  intros E n z H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
  unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_mod. lia.
Qed.

Lemma c3B_in256 : forall (P : Z -> bool) v, 0 <= v < 256 -> forallb P (map Z.of_nat (seq 0 256)) = true -> P v = true.
Proof.
  intros P v Hv H. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat v).
  split; [lia | apply in_seq; lia].
Qed.

Lemma c3B_sext_val : forall v, 0 <= v < 256 ->
  zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL v 56)) 56) = c3_sext8 v mod 2 ^ 64.
Proof.
  intros v Hv. apply Z.eqb_eq.
  apply (c3B_in256 (fun z => zcanon (zalu_raw 63 64 ALU_SRA (zcanon (zalu_raw 63 64 ALU_SLL z 56)) 56) =? c3_sext8 z mod 2 ^ 64) v Hv).
  vm_compute. reflexivity.
Qed.

Lemma c3B_land8 : forall op, 0 <= op < 256 -> Z.land op 8 = 0 \/ Z.land op 8 = 8.
Proof.
  intros op Hop.
  pose proof (c3B_in256 (fun z => (Z.land z 8 =? 0) || (Z.land z 8 =? 8)) op Hop ltac:(vm_compute; reflexivity)) as H.
  apply orb_true_iff in H. destruct H as [H|H]; apply Z.eqb_eq in H; [left|right]; exact H.
Qed.

(* s7 at 0x80840 (slli / srai 0x38): the index byte sign-extended. *)
Lemma c3B_den_sext : forall E v, ew E 24 = w64 v -> 0 <= v < 256 ->
  alu64 ALU_SRA (alu64 ALU_SLL (ew E 24) (Z_to_bv 64 56)) (Z_to_bv 64 56) = w64 (c3_sext8 v).
Proof.
  intros E v H Hv.
  assert (D : alu64 ALU_SRA (alu64 ALU_SLL (ew E 24) (Z_to_bv 64 56)) (Z_to_bv 64 56) =
    sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL (SOff 24 0) (SLit 56)) (SLit 56)))
    by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
  rewrite D, denot_lit_U, !U_SAlu, (c3B_U_atom E 24 v H), !U_SLit.
  change (zcanon 56) with 56. rewrite (Z.mod_small v) by lia.
  rewrite c3B_sext_val by exact Hv. apply c3B_w64_mod.
Qed.

Lemma c3B_den_sext0 : forall E v, ew E 24 = w64 v -> 0 <= v < 256 ->
  alu64 ALU_ADD (alu64 ALU_SRA (alu64 ALU_SLL (ew E 24) (Z_to_bv 64 56)) (Z_to_bv 64 56)) (Z_to_bv 64 0) = w64 (c3_sext8 v).
Proof.
  intros E v H Hv.
  assert (D : alu64 ALU_ADD (alu64 ALU_SRA (alu64 ALU_SLL (ew E 24) (Z_to_bv 64 56)) (Z_to_bv 64 56)) (Z_to_bv 64 0) =
    sv_denot E (SAlu ALU_ADD (SAlu ALU_SRA (SAlu ALU_SLL (SOff 24 0) (SLit 56)) (SLit 56)) (SLit 0)))
    by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
  rewrite D, denot_lit_U, !U_SAlu, (c3B_U_atom E 24 v H), !U_SLit.
  change (zcanon 56) with 56. change (zcanon 0) with 0. rewrite (Z.mod_small v) by lia.
  rewrite c3B_sext_val by exact Hv. cbn [zalu_raw]. rewrite Z.add_0_r. unfold zcanon, M64. rewrite Zmod_mod.
  apply c3B_w64_mod.
Qed.

(* s9 at 0x8082c: op & 8. *)
Lemma c3B_den_and8 : forall E op, ew E 23 = w64 op -> 0 <= op < 256 ->
  alu64 ALU_AND (ew E 23) (Z_to_bv 64 8) = w64 (Z.land op 8).
Proof.
  intros E op H Hop.
  assert (D : alu64 ALU_AND (ew E 23) (Z_to_bv 64 8) = sv_denot E (SAlu ALU_AND (SOff 23 0) (SLit 8)))
    by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
  rewrite D, denot_lit_U, U_SAlu, (c3B_U_atom E 23 op H), U_SLit.
  change (zcanon 8) with 8. rewrite (Z.mod_small op) by lia. cbn [zalu_raw].
  unfold zcanon, M64. apply c3B_w64_mod.
Qed.

(* a2 at 0x80838: the name argument, op & 8 ? NULL : q. *)
Lemma c3B_den_sel : forall E op q, ew E 23 = w64 op -> 0 <= op < 256 -> ew E 10 = w64 q -> 0 <= q < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_AND (ew E 23) (Z_to_bv 64 8)) (Z_to_bv 64 3)) (Z_to_bv 64 (-1))) (ew E 10)
  = w64 (c3_sel_q op q).
Proof.
  intros E op q H23 Hop H10 Hq.
  assert (D : alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_AND (ew E 23) (Z_to_bv 64 8)) (Z_to_bv 64 3)) (Z_to_bv 64 (-1))) (ew E 10)
    = sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_AND (SOff 23 0) (SLit 8)) (SLit 3)) (SLit (-1))) (SOff 10 0)))
    by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
  rewrite D, denot_lit_U, !U_SAlu, (c3B_U_atom E 23 op H23), (c3B_U_atom E 10 q H10), !U_SLit.
  change (zcanon 8) with 8. change (zcanon 3) with 3. change (zcanon (-1)) with (2 ^ 64 - 1).
  rewrite (Z.mod_small op), (Z.mod_small q) by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
  unfold c3_sel_q. destruct (c3B_land8 op Hop) as [E8 | E8]; rewrite E8.
  - change (zcanon (zcanon (Z.shiftr (zcanon 0) 3) + (2 ^ 64 - 1))) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. unfold zcanon, M64. rewrite !Zmod_mod. apply c3B_w64_mod.
  - change (zcanon (zcanon (Z.shiftr (zcanon 8) 3) + (2 ^ 64 - 1))) with 0.
    rewrite Z.land_0_l. reflexivity.
Qed.

Lemma c3B_pw_self : forall {X} (R : X -> X -> Prop) l1 l2 x, In x l1 -> pairwise R (l1 ++ x :: l2) -> R x x.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros l2 x Hin H; [destruct Hin|].
  cbn [app pairwise] in H. destruct H as [Hf Hp]. destruct Hin as [<- | Hin].
  - rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. left. reflexivity.
  - exact (IH l2 x Hin Hp).
Qed.

Lemma c3B_aview_eq : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' E a. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* The shadow byte AR fixes for each registered global (its size): BLxLib's cells of the const law. *)
Lemma c3B_gshadow : forall ly S (W : world SEGS) mem md g sz, In (g, sz) LX_GLOBS -> AR SEGS B ly S W mem md ->
  aview SEGS (w_H W) mem (shadow_addr (VAL (A_OBJ g))) = Some sz.
Proof.
  intros ly S W mem md g sz Hin HAR. destruct HAR as (M & _).
  pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
  assert (Hc : In (z1 (ANum (shadow_addr (VAL (A_OBJ g)))) sz) (as_const B ly)).
  { apply (blx_cells B (lh_glob B MT HY) ly). unfold lx_glob_cells. apply in_flat_map.
    exists (g, sz). split; [exact Hin|]. cbn [fst snd]. left. reflexivity. }
  assert (Hsz : 0 <= sz < 256)
    by (cbv [LX_GLOBS In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
  specialize (C _ Hc). unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
  specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. rewrite C. f_equal.
  unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hsz.
Qed.

Definition C3B_G : list (Z * Z) := [(VAL (A_OBJ 10), 3); (VAL (A_OBJ 11), 1)].

(* "%s" and "" as registered globals: their shadow byte holds their size (one partial granule each). *)
Lemma c3B_globs : globs_marked SEGS B C3B_G.
Proof.
  intros ly S W mem md q sz Hin HAR.
  assert (Hg : (q = VAL (A_OBJ 10) /\ sz = 3 /\ In (10%nat, 3) LX_GLOBS) \/ (q = VAL (A_OBJ 11) /\ sz = 1 /\ In (11%nat, 1) LX_GLOBS)).
  { unfold C3B_G in Hin. destruct Hin as [E | [E | []]]; injection E as <- <-; [left | right];
      (split; [reflexivity | split; [reflexivity | unfold LX_GLOBS; cbn [In]; tauto]]). }
  destruct Hg as [(-> & -> & Hg) | (-> & -> & Hg)];
    (split; [apply (blx_al B (lh_glob B MT HY)) in Hg; cbn [fst] in Hg;
             apply Z.mod_divide in Hg; [|lia]; apply Z.mod_divide; [lia|]; destruct Hg as [x Hx]; exists (4 * x); lia|]);
    (split; [lia|]); intros i Hi; change ((3 + 7) / 8) with 1 in Hi; change ((1 + 7) / 8) with 1 in Hi;
    assert (i = 0) as -> by lia; cbn -[shadow_of_addr];
    rewrite Z.add_0_r; exact (c3B_gshadow ly S W mem md _ _ Hg HAR).
Qed.

(* ---- the phase: the point C3_RN's data ---- *)
Section c.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Variable pos : nat.
Variables r fab op idxb q : Z.
Variables bs nm : list byte.
Hypothesis HB : lx_base B MT cx.
Hypothesis HJ : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
  [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
(* Rounding mode 0 at this FP state: reac_boxreg_set_name's spec takes it (freeze change 4). *)
Hypothesis HRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HSN : forall fx' : YK11.FPState, lx_fxr fx fx' -> lx_from B MT POST (C3_SN (fx := fx') B MT i).
Hypothesis HBD : C3_body B MT LP_RN i cx fp k acc ly3 S3 W3 ms3 pos r fab op q bs bs nm.
Hypothesis Hidxb : 0 <= idxb < 256.
Hypothesis R10 : getr (ms_regs ms3) 10 = w64 q.
Hypothesis R23 : getr (ms_regs ms3) 23 = w64 op.
Hypothesis R24 : getr (ms_regs ms3) 24 = w64 idxb.

Lemma c3B_blk : ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (q, c3_nlen nm + 1)].
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HBD))))). Qed.

Lemma c3B_AR : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof. exact (proj1 HJ). Qed.

Lemma c3B_rin : In (r, LX_REG) (ablocks B ly3 S3).
Proof. rewrite c3B_blk. apply in_or_app. right. left. reflexivity. Qed.

Lemma c3B_qin : In (q, c3_nlen nm + 1) (ablocks B ly3 S3).
Proof. rewrite c3B_blk. apply in_or_app. right. right. left. reflexivity. Qed.

Lemma c3B_lc_in : forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3).
Proof. intros p n H. rewrite c3B_blk. apply in_or_app. left. exact H. Qed.

(* The registry block is none of the caller's blocks (the blocks are pairwise apart). *)
Lemma c3B_r_new : ~ In (r, LX_REG) (ablocks B (lc_ly cx) (lc_S cx)).
Proof.
  intros Hin.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG c3B_AR c3B_rin) as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite c3B_blk, map_app in Hpw. cbn [map] in Hpw.
  pose proof (c3B_pw_self zdisjoint _ _ _ (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin) Hpw) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. change (req_size LX_REG) with 288 in Hz. lia.
Qed.

Lemma c3B_apart : forall p n, In (p, n) (ablocks B ly3 S3) -> 0 < n -> (p, n) <> (r, LX_REG) ->
  p + n <= r \/ r + 288 <= p.
Proof.
  intros p n Hin Hn Hne.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG c3B_AR c3B_rin) as (_ & _ & _ & _ & _ & Hpw & _).
  assert (Hne' : (p, req_size n) <> (r, req_size LX_REG)).
  { intros E. injection E as E1 E2. rewrite c3_req in E2 by exact Hn. apply Hne. rewrite E1, E2. reflexivity. }
  destruct (c3_pw_in zdisjoint _ (p, req_size n) (r, req_size LX_REG) Hpw
    (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin)
    (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ c3B_rin) Hne') as [Hz | Hz];
    unfold zdisjoint in Hz; cbn [fst snd] in Hz; rewrite (c3_req n) in Hz by exact Hn;
    change (req_size LX_REG) with 288 in Hz; lia.
Qed.

Definition c3B_rs : list (Z * Z) := [(q, c3_nlen nm + 1)].

Lemma c3B_nl : 0 <= c3_nlen nm <= 47.
Proof. pose proof HBD as (_ & _ & _ & _ & _ & _ & Hnl & _). unfold c3_nlen in *. lia. Qed.

Lemma c3B_rgeo : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ in_app r 288.
Proof.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG c3B_AR c3B_rin) as (H1 & H2 & H3 & H4 & _).
  change (req_size LX_REG) with 288 in H3, H4. tauto.
Qed.

(* No byte the phase's facts speak about (the keep set of BoxBLxSeat.v, with the name block) is in set_name's
   footprint, the registry. *)
Lemma c3B_fp : forall a, lx_keep_at cx fp c3B_rs a -> ~ inFP [(r, r + REG_SIZEB)] a.
Proof.
  intros a Ha (x & Hx & Hxa). destruct Hx as [<- | []]. cbn [fst snd] in Hxa. unfold REG_SIZEB in Hxa.
  pose proof c3B_rgeo as (Hr16 & Hr0 & Hr1 & Hria).
  pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPceil & SP47 & SPsp1 & SPal).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - lia.
  - pose proof HB as (_ & _ & _ & Hpn & _).
    destruct Hpn as [Hn0 | (Hnpos & Hin0)]; [lia|].
    assert (Hne : (lc_p cx, lc_n cx) <> (r, LX_REG)) by (intros E; apply c3B_r_new; rewrite <- E; exact Hin0).
    destruct (c3B_apart (lc_p cx) (lc_n cx) (c3B_lc_in _ _ Hin0) ltac:(lia) Hne) as [Hd | Hd]; lia.
  - pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp c3B_AR c3B_rin (lx_fin fp S3 HFR)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in Hd.
    change (req_size LX_REG) with 288 in Hd. change (fs_frame_bytes LX_CID) with 512 in Hd, Ha. lia.
  - change (fs_frame_bytes LX_CID / 8) with 64 in Ha. rewrite HSHeq in Ha.
    revert Ha Hxa Hria HF0 HFc C1 C2 C3 C4 C5. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. clear.
    intros. Z.div_mod_to_equations. lia.
  - apply Exists_exists in Ha as (y & Hy & Hya). destruct Hy as [<- | []]. cbn [fst snd] in Hya.
    pose proof c3B_nl as Hnl.
    assert (Hne : (q, c3_nlen nm + 1) <> (r, LX_REG)) by (intros E; injection E as _ E2; unfold LX_REG in E2; lia).
    destruct (c3B_apart q (c3_nlen nm + 1) c3B_qin ltac:(lia) Hne) as [Hd | Hd]; lia.
Qed.

(* The call chain set_name gets at sp1 (BoxBLxDefs.v lx_achain at the phase's layout). *)
Lemma c3B_achain : forall memc mdc, (forall x, memc x = ms_mem ms3 x) ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3
    memc mdc k ->
  achain ly3 (aview SEGS (w_H W3) memc) (lsp1 cx) (lsp0 cx) (lch cx).
Proof.
  intros memc mdc Hm HJc.
  pose proof HBD as ((_ & _ & _ & _ & _ & _ & _ & SV & _) & _).
  pose proof HB as ((HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HJc as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs1 & Hs2 & Hs32). pose proof asan_consts as (C1 & _).
  destruct SV as (Sra & Sj). unfold lview in Sra, Sj.
  apply (achain_ly_top (lc_ly cx) ly3 _ _ _ _ Etop).
  eapply lx_achain.
  - exact Hch.
  - unfold lsp0 in *. lia.
  - unfold lsp0 in *. lia.
  - lia.
  - exact Hra4.
  - intros a Ha. apply F1; [lia | unfold LX_STK; lia].
  - unfold rdword in Sra |- *. rewrite !(c3B_aview_eq (w_H W3) (ms_mem ms3) memc Hm). exact Sra.
  - pose proof (Sj 0 ltac:(lia)) as S0. rewrite Z.mul_0_r, Z.sub_0_r in S0.
    unfold rdword in S0 |- *. rewrite !(c3B_aview_eq (w_H W3) (ms_mem ms3) memc Hm). rewrite S0. reflexivity.
  - lia.
Qed.

Lemma c3B_call : forall (regsc : bvmap 5 word) memc mdc,
  (forall x, memc x = ms_mem ms3 x) ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3
    memc mdc k ->
  (forall n, In n [2; 3; 4; 8; 9; 18; 20; 21; 22; 26; 27] -> getr regsc (Z_to_bv 5 n) = getr (ms_regs ms3) (Z_to_bv 5 n)) ->
  getr regsc 1 = Z_to_bv 64 (BASE + LP_SN) ->
  getr regsc 10 = w64 r -> getr regsc 11 = w64 (c3_sext8 idxb) -> getr regsc 12 = w64 (c3_sel_q op q) ->
  getr regsc 19 = w64 q -> getr regsc 23 = w64 (c3_sext8 idxb) -> getr regsc 24 = w64 idxb ->
  getr regsc 25 = w64 (Z.land op 8) ->
  SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA BB_reac_boxreg_set_name)) memc (seg_rom SEGS)) mdc) (POST cx).
Proof.
  intros regsc memc mdc Hm HJc KR Hra Q10 Q11 Q12 Q19 Q23 Q24 Q25.
  pose proof HBD as (HBODY & Hi & Hk & Hacc & Hblk & Hq4096 & Hnl & Hnm & Hreg & Hinv & Hfab & Hprev & Hop3 & Hop
    & Hcur & Hloop & H58 & R20 & R21 & R26 & R27).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG & HS10 & HS18 & HS80 & HINP).
  pose proof HREGS as (L2 & L8 & L9 & L3 & L4 & L18 & L22).
  pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPceil & SP47 & SPsp1 & SPal).
  pose proof c3B_rgeo as (Hr16 & Hr0 & Hr1 & Hria).
  pose proof c3B_nl as Hnl'.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _).
  pose proof Hinv as ((HLbs & HB1 & _) & _).
  pose proof (proj1 HJc) as HARc.
  assert (G2 : getr regsc 2 = w64 (lsp1 cx)) by (exact (eq_trans (KR 2 ltac:(cbn; tauto)) L2)).
  assert (G3 : getr regsc 3 = w64 (as_gp B)) by (exact (eq_trans (eq_trans (KR 3 ltac:(cbn; tauto)) L3) Hgp)).
  assert (G4 : getr regsc 4 = w64 (as_tp B)) by (exact (eq_trans (eq_trans (KR 4 ltac:(cbn; tauto)) L4) Htp)).
  assert (G8 : getr regsc 8 = w64 (lsp0 cx)) by (exact (eq_trans (KR 8 ltac:(cbn; tauto)) L8)).
  assert (Hsp : spZ regsc = lsp0 cx + (lsp1 cx - lsp0 cx)).
  { unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Ho16 : (lsp1 cx - lsp0 cx) mod 16 = 0) by lia.
  assert (HPRE : afn_pre SEGS B REAC_BOXREG_SET_NAME_STKB ly3 S3 W3 regsc memc mdc (lch cx)).
  { apply (afn_pre_at SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
             ly3 S3 W3 memc mdc k regsc REAC_BOXREG_SET_NAME_STKB (lsp1 cx - lsp0 cx) (lch cx) HJc Hsp Ho16).
    - lia.
    - unfold REAC_BOXREG_SET_NAME_STKB, ESTACK. lia.
    - unfold REAC_BOXREG_SET_NAME_STKB, ESTACK, LX_STK. lia.
    - rewrite Hra. apply ret_ok_codeptr_v; [unfold LP_SN; lia | reflexivity].
    - unfold raZ. rewrite Hra. pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)) as HBLO.
      pose proof pa_B_ok as (HB0 & HB1' & _).
      rewrite unsigned_lit_small by (unfold LP_SN; lia). unfold LP_SN. lia.
    - exact G3.
    - exact G4.
    - rewrite Hsp. replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia. unfold s0Z. rewrite G8. unfold w64.
      rewrite unsigned_lit_small by lia. exact (c3B_achain memc mdc Hm HJc). }
  pose proof (lh_glob B MT HY) as GL.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof (blx_marg B GL (10%nat, 3) ltac:(unfold LX_GLOBS; cbn [In]; tauto)) as M10.
  pose proof (blx_marg B GL (11%nat, 1) ltac:(unfold LX_GLOBS; cbn [In]; tauto)) as M11.
  pose proof (blx_rom_bytes B GL (10%nat, [37; 115; 0]) ltac:(unfold LX_GLOB_BYTES; cbn [In]; tauto)) as RB10.
  cbn [fst snd] in M10, M11, RB10.
  rewrite pa_sigma_reac_boxreg_set_name.
  (* set_name returns at SOME FP state fx' (apost_baseF); the call is bound with SRr_bind and the landing on C3_SN is
     taken at fx'. A Theorem Labs lane's srr_fx_continue (lib/A/Rt/FMsnprintfSx.v) does not apply here: its post asks rounding mode
     0 of every returned state's fcsr, and apost_baseF's left disjunct (fp_csr fx' = fp_csr fx, set_name's two early
     returns) is not covered; apost_baseF's two FP facts are lx_fxr fx fx'. *)
  eapply SRr_bind.
  { apply (lh_set_name B MT HY ly3 S3 W3 regsc memc mdc (lch cx) r (c3_sext8 idxb) (c3_sel_q op q) bs (c3_sel_s op nm)
             C3B_G HPRE).
    - exact (lx_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HRO).
    - exact Q10.
    - exact Q11.
    - exact Q12.
    - unfold c3_sext8. destruct (Z.ltb_spec idxb 128); lia.
    - exact c3B_rin.
    - exact HLbs.
    - intros x Hx. rewrite (c3B_aview_eq (w_H W3) (ms_mem ms3) memc Hm). apply Hreg. unfold REG_SIZEB, LX_REG in *. lia.
    - exact HB1.
    - unfold c3_sel_q, c3_sel_s. destruct (Z.land op 8 =? 0).
      + apply (c3_name_ok B MT HY ly3 S3 W3 memc mdc (spZ regsc) r q nm HARc).
        * exact c3B_qin.
        * exact c3B_rin.
        * unfold c3_nlen in Hnl'. lia.
        * intros j Hj. rewrite (c3B_aview_eq (w_H W3) (ms_mem ms3) memc Hm). exact (Hnm j Hj).
        * rewrite Hsp. unfold REAC_BOXREG_SET_NAME_STKB, ESTACK. lia.
      + left. split; reflexivity.
    - exact (blx_isv B GL).
    - exact c3B_globs.
    - exact RB10.
    - unfold C3B_G. left. reflexivity.
    - lia.
    - lia.
    - exact (blx_fmt_got B GL).
    - exact (proj1 (proj2 (blx_rom_strs B GL))).
    - unfold C3B_G. right. left. reflexivity.
    - lia.
    - lia.
    - exact HRM. }
  cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & HF1 & HF2 & HJ1 & HP & (-> & -> & -> & _ & HRB)).
  assert (HFX : lx_fxr fx fx') by exact (conj HF1 HF2).
  rewrite Hra.
  (* the caller's journal across the call: the callee's footprint is the registry, a block of this phase *)
  assert (HJ2 : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
                  ([] ++ [(LX_CID, fp)]) ly3 S3 W3 mem2 md2 (k + 0)).
  { eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJc | exact HJ1 | | |].
    - rewrite Hsp. unfold REAC_BOXREG_SET_NAME_STKB, ESTACK, LX_STK. lia.
    - rewrite Hsp. lia.
    - intros a (x & Hx & Hxa). destruct Hx as [<- | []]. cbn [fst snd] in Hxa. right.
      exists r, LX_REG. split; [exact c3B_rin|]. split; [exact c3B_r_new|].
      change (req_size LX_REG) with 288. unfold REG_SIZEB in Hxa. lia. }
  rewrite Z.add_0_r in HJ2. cbn [app] in HJ2.
  rewrite Hsp in HJ1. replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJ1 by lia.
  assert (Hrs : Forall (fun x => exists n, In (fst x, n) (ablocks B ly3 S3) /\ 0 <= snd x <= req_size n) c3B_rs).
  { apply Forall_cons; [|apply Forall_nil]. exists (c3_nlen nm + 1). cbn [fst snd].
    split; [exact c3B_qin|]. rewrite c3_req by lia. lia. }
  assert (KP : lx_keep cx fp W3 c3B_rs (ms_mem ms3) mem2).
  { apply (lx_keep_trans cx fp W3 c3B_rs (ms_mem ms3) memc mem2).
    - intros a _. exact (c3B_aview_eq (w_H W3) (ms_mem ms3) memc Hm a).
    - exact (lx_keep_call_fp B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR c3B_rs [(r, r + REG_SIZEB)]
               REAC_BOXREG_SET_NAME_STKB memc mdc mem2 md2 0 ltac:(lia) c3B_lc_in Hrs c3B_fp HJ1). }
  assert (KR2 : forall n, In n [2; 3; 4; 8; 9; 18; 20; 21; 22; 26; 27] ->
                  getr regs2 (Z_to_bv 5 n) = getr (ms_regs ms3) (Z_to_bv 5 n)).
  { intros n Hn. rewrite (HP n) by (unfold acallee_saved; cbv [In] in Hn; lia). exact (KR n Hn). }
  assert (KC : forall n, In n [19; 23; 24; 25] -> getr regs2 (Z_to_bv 5 n) = getr regsc (Z_to_bv 5 n)).
  { intros n Hn. apply HP. unfold acallee_saved; cbv [In] in Hn; lia. }
  set (ms' := @mkst fx' regs2 (Z_to_bv 64 (BASE + LP_SN)) mem2 (seg_rom SEGS)).
  assert (KP' : lx_keep cx fp W3 c3B_rs (ms_mem ms3) (ms_mem ms')) by exact KP.
  change (SRr SEGS W3 (mkCfg ms' md2) (POST cx)).
  apply (HSN fx' HFX cx fp k acc ly3 S3 W3 ms' md2 HB HJ2 HFR HMO).
  exists pos, r, fab, op, idxb, q, bs, nm.
  split.
  { split.
    { unfold lx_body. do 6 (split; [reflexivity|]).
      split.
      { unfold lregs. cbn [ms_regs ms'].
        split; [exact (eq_trans (KR2 2 ltac:(cbn; tauto)) L2)|].
        split; [exact (eq_trans (KR2 8 ltac:(cbn; tauto)) L8)|].
        split; [exact (eq_trans (KR2 9 ltac:(cbn; tauto)) L9)|].
        split; [exact (eq_trans (KR2 3 ltac:(cbn; tauto)) L3)|].
        split; [exact (eq_trans (KR2 4 ltac:(cbn; tauto)) L4)|].
        split; [exact (eq_trans (KR2 18 ltac:(cbn; tauto)) L18)|].
        exact (eq_trans (KR2 22 ltac:(cbn; tauto)) L22). }
      split; [exact (lx_saved_keep B MT cx fp W3 HB c3B_rs ms3 ms' KP' HSAVED)|].
      split; [exact (lx_shadow_keep cx fp W3 c3B_rs ms3 ms' LSH_iter KP' ltac:(vm_compute; congruence) HSH)|].
      split; [exact (lx_flag_keep cx fp W3 c3B_rs ms3 ms' KP' HFLAG)|].
      split; [exact (lx_slot_keep B MT cx fp W3 HB c3B_rs ms3 ms' 0x10 _ KP' ltac:(lia) ltac:(lia) HS10)|].
      split; [exact (lx_slot_keep B MT cx fp W3 HB c3B_rs ms3 ms' 0x18 _ KP' ltac:(lia) ltac:(lia) HS18)|].
      split; [exact (lx_slot_keep B MT cx fp W3 HB c3B_rs ms3 ms' 0x80 _ KP' ltac:(lia) ltac:(lia) HS80)|].
      exact (lx_input_keep cx fp W3 c3B_rs ms3 ms' KP' HINP). }
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact Hblk|].
    split; [exact Hq4096|]. split; [exact Hnl|].
    split.
    { intros j Hj. unfold lview. rewrite (KP' (q + j)); [exact (Hnm j Hj)|].
      right; right; right; right. apply Exists_cons_hd. cbn [fst snd]. lia. }
    split.
    { intros x Hx. unfold lview. cbn [ms_mem ms']. apply HRB. unfold REG_SIZEB, LX_REG in *. lia. }
    split; [exact Hinv|]. split; [exact Hfab|].
    split; [exact (lx_prev_keep cx fp W3 c3B_rs ms3 ms' bs KP' Hprev)|].
    split; [exact Hop3|]. split; [exact Hop|].
    split; [exact (lx_cur_keep B MT cx fp W3 HB c3B_rs ms3 ms' pos KP' Hcur)|].
    split; [exact (lx_slots_loop_keep B MT cx fp W3 HB c3B_rs ms3 ms' r fab KP' Hloop)|].
    split; [exact (lx_slot_keep B MT cx fp W3 HB c3B_rs ms3 ms' 0x58 _ KP' ltac:(lia) ltac:(lia) H58)|].
    cbn [ms_regs ms'].
    split; [exact (eq_trans (KR2 20 ltac:(cbn; tauto)) R20)|].
    split; [exact (eq_trans (KR2 21 ltac:(cbn; tauto)) R21)|].
    split; [exact (eq_trans (KR2 26 ltac:(cbn; tauto)) R26)|].
    exact (eq_trans (KR2 27 ltac:(cbn; tauto)) R27). }
  split; [exact Hidxb|]. cbn [ms_regs ms'].
  split; [exact (eq_trans (KC 19 ltac:(cbn; tauto)) Q19)|].
  split; [exact (eq_trans (KC 23 ltac:(cbn; tauto)) Q23)|].
  split; [exact (eq_trans (KC 24 ltac:(cbn; tauto)) Q24)|].
  exact (eq_trans (KC 25 ltac:(cbn; tauto)) Q25).
Qed.

Lemma c3B_ewR : forall (regs : bvmap 5 word) n (rr : bv 5),
  Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr.
Proof.
  intros regs n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* 0x80828 .. 0x8084c: s3 = name, s9 = op & 8, a2 = op & 8 ? NULL : name, s7 = (int8) idx, a0 = r, a1 = s7; the
   engine stops at set_name's entry (registers only: the state has no region), and c3B_call takes over. *)
Lemma c3B_walk : SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  pose proof HBD as (HBODY & Hi & Hk & Hacc & Hblk & Hq4096 & Hnl & Hnm & Hreg & Hinv & Hfab & Hprev & Hop3 & Hop
    & Hcur & Hloop & H58 & R20 & R21 & R26 & R27).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & _).
  pose proof c3B_rgeo as (Hr16 & Hr0 & Hr1 & Hria).
  pose proof asan_consts as (C1 & _).
  pose proof c3B_nl as Hnl'.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 q _ c3B_AR c3B_qin) as (_ & Hq0 & Hq1 & _).
  rewrite c3_req in Hq1 by lia.
  rewrite (c3B_ms_eq LP_RN ms3 Hpc Hresv Hsvc Hrom Hfreg Hfcsr).
  pose proof (c3B_seat W3 (ms_regs ms3) (ms_mem ms3) LP_RN) as HS.
  assert (SHOK : sh_ok SEGS C3B_Bx [] (Eimg (Ereg (ms_regs ms3) [])) (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E10 : ew E 10 = w64 q) by (subst E; rewrite (c3B_ewR _ 10 10%bv eq_refl); exact R10).
  assert (E20 : ew E 20 = w64 r) by (subst E; rewrite (c3B_ewR _ 20 20%bv eq_refl); exact R20).
  assert (E23 : ew E 23 = w64 op) by (subst E; rewrite (c3B_ewR _ 23 23%bv eq_refl); exact R23).
  assert (E24 : ew E 24 = w64 idxb) by (subst E; rewrite (c3B_ewR _ 24 24%bv eq_refl); exact R24).
  pose proof HJ as HJr.
  paj_run_tok RUN HS HJr SHOK C3B_span; [apply awr_ok_nil |].
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (19%bv : bv 5) Q19. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  apply (c3B_call (ms_regs ms) (ms_mem ms) _).
  - intros x. apply (HF x). intros (rg & Hin & _). destruct Hin.
  - exact HJr.
  - intros n Hn. rewrite HE in HS.
    pose proof (regs_kept_of_st_ok SEGS _ _ (restrict (w_H W3) ms) (ms_regs ms3) []
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 26; 27]) HS) as K.
    cbn [restrict ms_regs] in K. apply K; [| reflexivity | apply in_map; exact Hn].
    split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - rewrite Q1. reflexivity.
  - rewrite Q10. exact E20.
  - rewrite Q11. exact (c3B_den_sext0 E idxb E24 Hidxb).
  - rewrite Q12. exact (c3B_den_sel E op q E23 Hop E10 ltac:(lia)).
  - rewrite Q19. exact E10.
  - rewrite Q23. exact (c3B_den_sext E idxb E24 Hidxb).
  - rewrite Q24. exact E24.
  - rewrite Q25. exact (c3B_den_and8 E op E23 Hop).
Qed.

End c.

(* The call may reach the snprintf wrapper, which returns at SOME FP state fx' (lx_fxr fx fx'); the segment lands on
   C3_SN taken at fx' (BoxBLxCase3Defs.v c3_segB_ok, a Theorem Labs lane's binding shape for a cross-call segment). *)
Theorem c3_segB : forall POST i,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx', lx_fxr fx fx' -> lx_from B MT POST (C3_SN (fx := fx') B MT i)) -> lx_from B MT POST (C3_RN B MT i).
Proof using HY.
  intros POST i HRM HSN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (pos & r & fab & op & idxb & q & bs & nm & HBD & Hidxb & R10 & R19 & R23 & R24).
  exact (c3B_walk POST i cx fp k acc ly3 S3 W3 ms3 md3 pos r fab op idxb q bs nm HB HJ HFR HMO HRM HSN HBD Hidxb R10 R23 R24).
Qed.

End a.
