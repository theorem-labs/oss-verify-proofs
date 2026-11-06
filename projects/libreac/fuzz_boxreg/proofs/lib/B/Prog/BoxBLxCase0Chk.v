(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module names changed; 242 of its 323 lines of code are new or changed and 899 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of LLVMFuzzerTestOneInput, the checks after reac_boxreg_declare returned
   (0x805a4 .. 0x808f8): what the pieces D -> BC -> SC -> F -> FR share, and the seat they all sit on.

   Every one of those pieces starts at a cut of BoxBLxCase0Defs.v inside the same loop turn, so the machine
   state has the same shape: the turn's slots (lslots_loop, the turn number, r->n, want, the shifted base, the
   name) and, when a row was placed, the new row at rw = r + 56 n inside the registry block. The seat below
   states that state as the engine's symbolic state once, with
   - the spill slots of the turn as the chunks of the spill region (nothing in these pieces writes a slot, but
     the engine's write window for the spill region is the whole [0, 0x98), so each slot a piece reads or a cut
     keeps is carried as a chunk);
   - the shadow address of r->n (the slot 0x40) as the engine's shadow-token shape
     `SHADOW_OFF + (r + 280) >> 3` over the atom of r, so that the ASan check of r->n resolves through the
     shadow token (YCbn.v tok_load) instead of stopping the run;
   - the new row as a region of its own (the base, width and pinned fields the checks read), and the two shadow
     entries (the registry block and the row) that make every ASan check of those bytes a covered load.
   The open values of the turn (the name, ~r, ~prev, want, the cursor, the row's base, the row, r->n, nch, the
   base shifted to the top byte and the turn number) are atoms 48 .. 59: an open term in a chunk or a fact would
   make the engine's vm_compute walk the term.  *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC85 BoxBCJ BoxBRangeTaken.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd reac_boxreg_declare_c
  reac_boxreg_declare_inv LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow span of the walk (BoxBLxCase0TN.v c0tn_Bspan). *)
Definition C0C_SB : Z := 0x7fff8000.
Definition C0C_Bspan : Z * Z := (C0C_SB, C0C_SB + 2 ^ 44 - 1).
Definition C0C_Bx : sv := SOff LA_SB 0.

(* The piece's own atoms, 48 .. 59. *)
Definition C0A_NM : nat := 48%nat.    (* the name block                      *)
Definition C0A_NR : nat := 49%nat.    (* ~r                                  *)
Definition C0A_NP : nat := 50%nat.    (* ~prev                               *)
Definition C0A_WANT : nat := 51%nat.  (* want mod 2 ^ 64                     *)
Definition C0A_CUR : nat := 52%nat.   (* the input cursor                    *)
Definition C0A_REM : nat := 53%nat.   (* the bytes left                      *)
Definition C0A_B : nat := 54%nat.     (* the row's base field                *)
Definition C0A_RW : nat := 55%nat.    (* the row r + 56 n                    *)
Definition C0A_N : nat := 56%nat.     (* r->n before the call                *)
Definition C0A_NCH : nat := 57%nat.   (* nch                                 *)
Definition C0A_BSL : nat := 58%nat.   (* the base shifted to the top byte    *)
Definition C0A_I : nat := 59%nat.     (* the turn number                     *)

(* The spill slots of the turn.  0x40 is the shadow address of r->n in the engine's shape. *)
Definition c0c_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20%nat 280) (SLit 3)) (SOff LA_SB 0).
Definition c0c_slots : list (Z * sv) :=
  [(0x08, SLit 3); (0x10, SOff LA_F 0); (0x18, SOff LA_F 0);
   (0x28, SOff 20%nat 280); (0x30, SOff 27%nat 0); (0x38, SLit 0); (0x40, c0c_shx);
   (0x48, SOff C0A_N 0); (0x58, SOff C0A_I 0); (0x60, SOff C0A_NM 0);
   (0x68, SOff LA_F 32); (0x70, SOff C0A_NR 0); (0x78, SOff C0A_NP 0); (0x80, SOff LA_F 0);
   (0x88, SOff C0A_CUR 0); (0x90, SOff C0A_REM 0)].
(* The two slots only some of the pieces carry: want (0x20) and the base shifted to the top byte (0x50). *)
Definition c0c_want_slot : Z * sv := (0x20, SOff C0A_WANT 0).
Definition c0c_bsl_slot : Z * sv := (0x50, SOff C0A_BSL 0).

(* r and the row: the ranges the ASan checks of the registry read. *)
Definition c0c_facts : facts :=
  mkFacts (LX_AF ++ [(20%nat, mkAF 4096 0x7fffff800000 0); (C0A_RW, mkAF 4096 0x7fffff800000 0)]) [] [].
Definition c0c_SH : list shent := [mkSHE 20%nat 0 288; mkSHE C0A_RW 0 56].
Definition c0c_row (rcs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some C0A_RW) 0 56 0 0 rcs.
(* The fields of a placed row the checks read: base, nch, pinned. *)
Definition c0c_rcs (p : Z) : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 4 (SOff C0A_B 0)); YP09.mkChunk 12 (CVal 4 (SOff C0A_NCH 0));
   YP09.mkChunk 20 (CVal 4 (SLit p))].

Ltac c0c_ew := rewrite ?ew_havoc_old by lia.
(* The write windows of a check's state: the spill slots (inside the function's stack window), the frame
   (the function's own), everything else read-only. *)
Ltac c0c_awr cx fp EFA UB2 UB46 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp0 ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp0 b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) _ _ _ _ _ _ _ _ 2%nat (lsp1 cx - lsp0 cx));
    [reflexivity | c0c_ew; rewrite UB2; lia | cbn; lia | cbn; lia |]
  | eapply (awr_ok_cons_gen _ (YP09.mkRegion (Some 46%nat) _ _ _ _ _) _ _ _ _ _ _ _ _ 46%nat (lF cx fp));
    [reflexivity | c0c_ew; exact UB46
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists LX_CID, fp; split; [left; reflexivity|];
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA; change (fs_frame_bytes LX_CID) with 512; lia
    |] ].


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

Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTO := paj_run_to B LAWS.

(* The frame's address and the layout's top are the same in every layout of the journal
   (BoxBLxExit.v lx_layout_addrs / lx_achain_ly). *)
Lemma c0c_layout_addrs : forall n ly ly' cid pos, layout_le n ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos /\
  ly_top ly' = ly_top ly.
Proof.
  intros n ly ly' cid pos Hle.
  pose proof Hle as (_ & _ & _ & _ & _ & HF & _ & _ & Htop & _).
  unfold frame_addr, flag_addr. rewrite HF, Htop. auto.
Qed.

Lemma c0c_achain_ly : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch Ht H. unfold achain in *. rewrite Ht. exact H. Qed.

(* An atom with an offset, as the engine's chunks and the cuts' slots read it. *)
Lemma c0c_den_off : forall (Ex : env) n c v, ew Ex n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot Ex (SOff n c) = w64 (v + c).
Proof.
  intros Ex n c v H Hv Hvc. cbn [sv_denot]. rewrite H. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The bytes a run of a check leaves alone: everything outside the spill window. *)
Lemma c0c_mbyte_frame : forall (Ex : env) rs (m m' : word -> option byte) a,
  YP09.frame_of Ex rs m m' -> 0 <= a < 2 ^ 64 -> ~ YP09.in_wrange Ex rs a ->
  YP09.mbyte SEGS m' a = YP09.mbyte SEGS m a.
Proof.
  intros Ex rs m m' a HF Ha Hw. unfold YP09.mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hw.
Qed.



(* The piece's own atoms as words. *)
Definition c0c_ex (cx : lxcx) (fp : Z) (i pos2 : nat) (r nm want b rw nn nch bsl : Z) : list word :=
  [w64 nm; w64 (2 ^ 64 - 1 - r); w64 (2 ^ 64 - 1 - (lF cx fp + 64)); w64 (want mod 2 ^ 64);
   w64 (lc_p cx + Z.of_nat pos2); w64 (lc_n cx - Z.of_nat pos2); w64 b; w64 rw; w64 nn; w64 nch; w64 bsl;
   w64 (Z.of_nat i)].


Lemma c0c_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [Hf Hr]. split; [exact Hf | exact (IH l2 Hr H2)].
Qed.

Lemma c0c_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

(* The alignment of the realigned stack pointer, and a word an 8-byte chunk of a region fixes
   (BoxBLxExit.v lx_mod16 / lx_mod8 / xs_word, restated here so the checks do not depend on the exit). *)
Lemma c0c_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [x ->]. destruct Hb as [y ->]. apply Z.mod_divide; [lia|]. exists (2 * x - y). lia.
Qed.

Lemma c0c_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->].
  apply Z.mod_divide; [lia|]. exists (2 * x). lia.
Qed.

Lemma c0c_word : forall E ss (H : word -> bool) ms i nb b lo hi wlo whi cs off e v,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some nb) lo hi wlo whi cs) ->
  bv_unsigned (ew E nb) = b -> In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> rdword (aview SEGS H (ms_mem ms)) (b + off) = Some v.
Proof.
  intros E ss H ms i nb b lo hi wlo whi cs off e v HS Hi Hb Hc He Hv.
  apply (rdword_of_val_mem SEGS H (ms_mem ms)); [|exact Hv].
  pose proof (st_ok_region_nth E ss (restrict H ms) i _ HS Hi) as HR.
  exact (field_of_region E _ nb b cs lo hi wlo whi off 8%N e v HR Hb Hc He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* The fields of the new row the checks read, as chunks of the row's region: the base, the width and the pinned
   flag of reac_boxreg_declare_c.decl_row, from the registry's bytes (BoxBRangeTaken.v rt_vm4). *)
Lemma c0c_row_fld : forall (W3 : world SEGS) (ms3 : machine_state) (E : env) r bs b nch p s (off v : Z) (e : sv),
  lreg W3 ms3 r (c0_placed bs b nch p s) ->
  length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 ->
  0 <= off -> off + 4 <= 56 ->
  Boxreg.rd4 (reac_boxreg_declare_c.decl_row b nch p s) off = v ->
  0 <= v < 2 ^ 31 -> sv_denot E e = w64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (r + 56 * Boxreg.bx_n bs)
    (YP09.mkChunk off (CVal 4 e)).
Proof.
  intros W3 ms3 E r bs b nch p s off v e HRG HL Hn Hoff Hoff4 Hrdv Hv He.
  assert (HL' : length (c0_placed bs b nch p s) = 288%nat)
    by (unfold c0_placed; apply (LLVMFuzzerTestOneInput_case0.c0_decl_length bs b nch p s HL Hn)).
  assert (Hrd : Boxreg.rd4 (c0_placed bs b nch p s) (56 * Boxreg.bx_n bs + off) = v).
  { rewrite <- Hrdv. unfold Boxreg.rd4.
    change (c0_placed bs b nch p s) with (reac_boxreg_declare_c.decl_bytes bs b nch p s).
    rewrite (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b nch p s off 4 HL Hn ltac:(lia) ltac:(lia) ltac:(lia)).
    reflexivity. }
  apply (chunk_ok_val SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (r + 56 * Boxreg.bx_n bs) off 4%N e v He);
    [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
  replace (r + 56 * Boxreg.bx_n bs + off) with (r + (56 * Boxreg.bx_n bs + off)) by lia.
  rewrite <- Hrd.
  apply (rt_vm4 W3 (ms_mem ms3) r (56 * Boxreg.bx_n bs + off) (c0_placed bs b nch p s));
    [exact HL' | lia | lia | rewrite Hrd; lia |].
  intros j Hj. exact (HRG j ltac:(unfold LX_REG; lia)).
Qed.

(* rd4 of a field of a declared row (reac_boxreg_declare_inv.v decl_row_base / _nch / _pin). *)
Lemma c0c_rd_base : forall b k p s, -2 ^ 31 <= b < 2 ^ 31 -> Boxreg.rd4 (reac_boxreg_declare_c.decl_row b k p s) 8 = b.
Proof. intros b k p s Hb. apply BoxregUpd.rd4_le4; [exact Hb | apply reac_boxreg_declare_inv.decl_row_base]. Qed.
Lemma c0c_rd_nch : forall b k p s, -2 ^ 31 <= k < 2 ^ 31 -> Boxreg.rd4 (reac_boxreg_declare_c.decl_row b k p s) 12 = k.
Proof. intros b k p s Hk. apply BoxregUpd.rd4_le4; [exact Hk | apply reac_boxreg_declare_inv.decl_row_nch]. Qed.
Lemma c0c_rd_pin : forall b k p s, -2 ^ 31 <= p < 2 ^ 31 -> Boxreg.rd4 (reac_boxreg_declare_c.decl_row b k p s) 20 = p.
Proof. intros b k p s Hp. apply BoxregUpd.rd4_le4; [exact Hp | apply reac_boxreg_declare_inv.decl_row_pin]. Qed.

Lemma c0c_row_ok : forall (W3 : world SEGS) (ms3 : machine_state) (E : env) r bs b nch p s,
  lreg W3 ms3 r (c0_placed bs b nch p s) ->
  length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 ->
  0 <= b < 2 ^ 31 -> 0 <= nch < 2 ^ 31 -> 0 <= p < 2 ^ 31 ->
  ew E C0A_B = w64 b -> ew E C0A_NCH = w64 nch ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (r + 56 * Boxreg.bx_n bs)) (c0c_rcs p).
Proof.
  intros W3 ms3 E r bs b nch p s HRG HL Hn Hb Hnch Hp E54 E57.
  unfold c0c_rcs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (c0c_row_fld W3 ms3 E r bs b nch p s 8 b); try assumption; try lia.
    + apply c0c_rd_base. lia.
    + rewrite lx_sv_SOff0. exact E54.
  - apply (c0c_row_fld W3 ms3 E r bs b nch p s 12 nch); try assumption; try lia.
    + apply c0c_rd_nch. lia.
    + rewrite lx_sv_SOff0. exact E57.
  - apply (c0c_row_fld W3 ms3 E r bs b nch p s 20 p); try assumption; try lia.
    + apply c0c_rd_pin. lia.
    + cbn [sv_denot]. reflexivity.
Qed.

(* The seat of every piece: the common slots, the two the piece adds (sl2), the shadow entries of the registry
   block and of the row, and the row's own region. *)
Lemma c0c_wf : forall sl rcs,
  YP09.region_wf (lx_spill_region (lx_slot_chunks sl)) = true ->
  forallb (YP09.chunk_inside (c0c_row rcs)) rcs = true ->
  YP09.regions_wf (lx_regions LSH_iter (lx_slot_chunks sl) [] 0 0 0 0 [c0c_row rcs]) = true.
Proof.
  intros sl rcs Hs H. unfold lx_regions, lx_regions0. cbn [app YP09.regions_wf].
  replace (YP09.region_wf (c0c_row rcs)) with true. rewrite Hs. vm_compute. reflexivity.
Qed.

Lemma c0c_seat : forall cx fp k ly3 S3 W3 ms3 md3 (i pos2 : nat) pc r fab nm want b rw nn nch bsl sl2 rcs,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lx_body cx fp pc W3 ms3 LSH_iter ->
  lslots_loop cx fp W3 ms3 r fab ->
  lslot cx W3 ms3 0x58 (Z.of_nat i) -> lslot cx W3 ms3 0x48 nn -> lslot cx W3 ms3 0x60 nm ->
  lcur cx W3 ms3 pos2 -> (0 < length (lc_pl cx))%nat ->
  getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms3) 27 = w64 fab ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  In (r, LX_REG) (ablocks B ly3 S3) -> r <= rw -> rw + 56 <= r + 288 ->
  0 <= nn -> 0 <= nch -> 0 <= b ->
  lx_slots cx W3 ms3 (lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl)) sl2 ->
  YP09.region_wf (lx_spill_region (lx_slot_chunks (c0c_slots ++ sl2))) = true ->
  Forall (YP09.chunk_ok SEGS (lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl))
            (mrestrict (w_H W3) (ms_mem ms3)) rw) rcs ->
  forallb (YP09.chunk_inside (c0c_row rcs)) rcs = true ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl))
    (lx_ss pc (lx_sr LX_OVP) LSH_iter (lx_slot_chunks (c0c_slots ++ sl2)) [] 0 0 0 0 [c0c_row rcs] c0c_facts)
    (restrict (w_H W3) ms3) /\
  sh_ok SEGS C0C_Bx c0c_SH (lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl))
    (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 i pos2 pc r fab nm want b rw nn nch bsl sl2 rcs
    HB HJ HFR HBD Hsl H58 H48 H60 Hcur Hplen H20 H21 H27 Hmono Hrin Hrw1 Hrw2 Hnn Hnch Hb HSL2 HSWF HRC HRWF.
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG
    & HS10 & HS18 & HS80 & HINP).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in *.
  pose proof HB as (_ & _ & _ & Hpn & _).
  pose proof Hcur as (HcurL & Hcur88 & Hcur90).
  assert (Hn : 0 < lc_n cx < 2 ^ 26 /\ In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx))).
  { destruct Hpn as [Hn0 | Hn]; [unfold lc_n in Hn0; lia | exact Hn]. }
  destruct Hn as [Hnr Hpin].
  pose proof (Hmono _ _ Hpin) as Hpin3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin3) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
  assert (Hreq : req_size (lc_n cx) = lc_n cx)
    by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lc_n cx) 0) ltac:(lia)); reflexivity).
  rewrite Hreq in Hpceil, Hpia.
  set (E := lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl)).
  assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 _); exact HREGS).
  pose proof HE as (_ & _ & _ & _ & _ & HE32 & _ & HE46 & _).
  assert (EX : forall j, (j < 12)%nat ->
    ew E (LA_EX + j) = nth j (c0c_ex cx fp i pos2 r nm want b rw nn nch bsl) (w64 0))
    by (intros j Hj; apply lx_env_ex; lia).
  assert (E48 : ew E C0A_NM = w64 nm) by exact (EX 0%nat ltac:(lia)).
  assert (E49 : ew E C0A_NR = w64 (2 ^ 64 - 1 - r)) by exact (EX 1%nat ltac:(lia)).
  assert (E50 : ew E C0A_NP = w64 (2 ^ 64 - 1 - (lF cx fp + 64))) by exact (EX 2%nat ltac:(lia)).
  assert (E52 : ew E C0A_CUR = w64 (lc_p cx + Z.of_nat pos2)) by exact (EX 4%nat ltac:(lia)).
  assert (E53 : ew E C0A_REM = w64 (lc_n cx - Z.of_nat pos2)) by exact (EX 5%nat ltac:(lia)).
  assert (E55 : ew E C0A_RW = w64 rw) by exact (EX 7%nat ltac:(lia)).
  assert (E56 : ew E C0A_N = w64 nn) by exact (EX 8%nat ltac:(lia)).
  assert (E59 : ew E C0A_I = w64 (Z.of_nat i)) by exact (EX 11%nat ltac:(lia)).
  assert (E20 : ew E 20%nat = w64 r)
    by (unfold E; rewrite (lx_env_reg cx fp _ _ 20 (20%bv : bv 5)) by reflexivity; exact H20).
  assert (E27 : ew E 27%nat = w64 fab)
    by (unfold E; rewrite (lx_env_reg cx fp _ _ 27 (27%bv : bv 5)) by reflexivity; exact H27).
  pose proof Hsl as (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  assert (RNG : forall off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64)
    by (intros off v Hv; exact (c0_rdword_range _ _ _ _ Hv)).
  pose proof (RNG _ _ S30) as Hfab. pose proof (RNG _ _ H48) as Hnn64.
  pose proof (RNG _ _ H60) as Hnm64. pose proof (RNG _ _ H58) as Hi64. pose proof (RNG _ _ S40) as Hsh64.
  unfold lc_n in *.
  assert (Hshx : sv_denot E c0c_shx = w64 (shadow_addr (r + 280))).
  { unfold c0c_shx. rewrite (denot_shx E 20%nat LA_SB 280 r SHADOW_OFF E20 HE32) by (unfold SHADOW_OFF; lia).
    reflexivity. }
  assert (HSL : lx_slots cx W3 ms3 E (c0c_slots ++ sl2)).
  { unfold lx_slots. apply Forall_app. split; [|exact HSL2]. unfold c0c_slots.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - exact (lx_slot_lit cx W3 ms3 E 0x08 3 S08 ltac:(lia)).
    - apply (lx_slot_atom cx W3 ms3 E 0x10 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS10 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x18 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS18 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x28 20%nat r 280); [exact S28 | exact E20 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x30 27%nat fab 0); [rewrite Z.add_0_r; exact S30 | exact E27 | lia | lia].
    - exact (lx_slot_lit cx W3 ms3 E 0x38 0 S38 ltac:(lia)).
    - rewrite Hshx. unfold w64. rewrite unsigned_lit_small by lia. exact S40.
    - apply (lx_slot_atom cx W3 ms3 E 0x48 C0A_N nn 0); [rewrite Z.add_0_r; exact H48 | exact E56 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x58 C0A_I (Z.of_nat i) 0);
        [rewrite Z.add_0_r; exact H58 | exact E59 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x60 C0A_NM nm 0); [rewrite Z.add_0_r; exact H60 | exact E48 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x68 LA_F (lF cx fp) 32); [exact S68 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x70 C0A_NR (2 ^ 64 - 1 - r) 0);
        [rewrite Z.add_0_r; exact S70 | exact E49 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x78 C0A_NP (2 ^ 64 - 1 - (lF cx fp + 64)) 0);
        [rewrite Z.add_0_r; exact S78 | exact E50 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x80 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS80 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x88 C0A_CUR (lc_p cx + Z.of_nat pos2) 0);
        [rewrite Z.add_0_r; exact Hcur88 | exact E52 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x90 C0A_REM (Z.of_nat (length (lc_pl cx)) - Z.of_nat pos2) 0);
        [rewrite Z.add_0_r; exact Hcur90 | exact E53 | lia | lia]. }
  assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact HE32 | unfold SHADOW_OFF; lia]).
  assert (U20 : U E (SOff 20%nat 0) = r) by (apply U_atom; [exact E20 | lia]).
  assert (U55 : U E (SOff C0A_RW 0) = rw) by (apply U_atom; [exact E55 | lia]).
  assert (B55 : bv_unsigned (ew E C0A_RW) = rw) by (rewrite E55; apply unsigned_lit_small; lia).
  assert (HREG : regs_ok E (lx_sr LX_OVP) (ms_regs ms3)).
  { apply lx_regs_ok; [apply lx_regs_ok_atoms | apply (lx_ovp_ok cx fp ms3 _); [exact HREGS | exact H21]]. }
  assert (HAF : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
  split.
  - apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR);
      [exact HE | exact HBD | exact HREG | exact HSL | apply Forall_nil | lia | lia | lia | lia | | | | | ].
    + exact (c0c_wf (c0c_slots ++ sl2) rcs HSWF HRWF).
    + apply Forall_cons; [|apply Forall_nil]. unfold c0c_row, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite B55. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact HRC].
    + cbn. tauto.
    + apply (lx_block_disj B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E C0A_RW rw r LX_REG 0 56 0 0 rcs
               LSH_iter (lx_slot_chunks (c0c_slots ++ sl2)) [] 0 0 0 0 HE Hrin B55);
        [lia | lia | change (req_size LX_REG) with 288; lia].
    + split; [|split; exact I]. unfold c0c_facts. cbn [f_atoms]. apply c0c_atoms_ok_app; [exact HAF|].
      cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E20, E55. unfold w64. rewrite !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      split; [repeat split; first [exact I | lia]|]. split; [repeat split; first [exact I | lia] | exact I].
  - unfold sh_ok, c0c_SH, C0C_Bx. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E r r LX_REG 0 288 20%nat HAR3 Hrin U32 U20);
        [lia | lia | change (req_size LX_REG) with 288; lia].
    + apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E rw r LX_REG 0 56 C0A_RW HAR3 Hrin U32 U55);
        [lia | lia | change (req_size LX_REG) with 288; lia].
Qed.
End a.
