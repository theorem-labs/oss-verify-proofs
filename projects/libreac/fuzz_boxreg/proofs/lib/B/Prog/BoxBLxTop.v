(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 790 of its 877 lines of code are new or changed and 844 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase1Read.v, with its module paths and module names changed; 843 of its 956 lines of code are new or changed and 764 lines of the source are left out. *)
(* The loop head of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (BoxBLxDefs.v's cuts): from LI_J (0x80258,
   turn i) the run reaches LI_X (0x80e54) when the input is used up, and LI_T (0x8034c) otherwise.
   0x80258 ld a1, in.n; beqz a1 -> 0x80e54. Else fuzz_u8 inline: in.n - 1, in.p + 1 (the UBSan pointer-overflow
   test bgeu s3 = 1, p + 1 at 0x80270 is refuted by p >= 4096), the shadow check of the input byte at p (the
   engine's shadow token; the input block's shadow, AR_shadow_law: lc_n > 0 makes it a block of the caller, so the
   __asan_report_load1 path is not taken), lbu s7 = op. Then mac's shadow byte := 6 (0x80290), the r & 3 test on
   the slot 0x38 (0), the shadow check of r->n through the slot 0x40 (the registry block's shadow byte of r + 280
   is 0), lw s10 = r->n = bx_n bs, prev's 36 shadow bytes := 0 (LSH_iter), and __asan_memcpy (F + 64, r, 288) at
   0x80348 (YCbq.v aj_intrin_at with lh_memcpy: the destination is the call's own side-stack frame, the source the
   registry block). Its return slot 0x8034c is LI_T's pc, with c = op & 3.
   The walk's symbolic states are this phase's own (atoms 0..31 the registers at 0x80258; 32 p + pos, 33 the bytes
   left, 34 op, 35 bx_n bs, 36 the shadow address of r + 280): the slots it reads and writes, the frame's shadow
   bytes, the input byte, r->n and its shadow byte. The cut facts outside the write windows carry over by the
   runs' frame_of and memcpy's frame. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregFind BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic states of the walk ---- *)
Definition LT_SB : Z := 0x7fff8000.
Definition lt_Bx : sv := SOff 18 0.
Definition lt_span : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition LT_K : nat := 512.
(* The slots the walk reads (0x08 = 3, 0x38 = 0, 0x40 = the shadow address of r->n, the cursor at 0x88 / 0x90) and
   the cursor's window. *)
Definition lt_slots : YP09.region := YP09.mkRegion (Some 9%nat) 8 0x98 0x88 0x98
  [YP09.mkChunk 0x08 (CVal 8 (SLit 3)); YP09.mkChunk 0x38 (CVal 8 (SLit 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 36 0));
   YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))].
(* When the input is used up, p may be any value: only the bytes left are read. *)
Definition lt_slots0 : YP09.region := YP09.mkRegion (Some 9%nat) 8 0x98 0x88 0x98
  [YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))].
(* The frame's shadow bytes (s6 = atom 22); the token run needs its window empty, the stores need [4, 44). *)
Definition lt_sh (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 22%nat) 0 64 wlo whi [].
Definition lt_in : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition lt_rn : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 35 0))].
Definition lt_rsh : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* The shadow window of the stores (mac's byte 4, prev's bytes 8 .. 43), with the bytes 5 .. 7 between them (0xf2)
   as chunks: the window loses every byte it does not carry. *)
Definition lt_sh2 : YP09.region := YP09.mkRegion (Some 22%nat) 0 64 4 44
  [YP09.mkChunk 5 (CVal 1 (SLit 242)); YP09.mkChunk 6 (CVal 1 (SLit 242)); YP09.mkChunk 7 (CVal 1 (SLit 242))].
Definition LT_SPLO : Z := 0x7fff7f800000.
Definition lt_facts0 : facts := mkFacts [(9%nat, mkAF LT_SPLO (2 ^ 47) 5); (33%nat, mkAF 0 0 0)] [] [].
Definition lt_facts1 : facts :=
  mkFacts [(9%nat, mkAF LT_SPLO (2 ^ 47) 5); (18%nat, mkAF LT_SB LT_SB 0); (19%nat, mkAF 1 1 0);
           (20%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 4096 140737479966720 0);
           (33%nat, mkAF 1 (2 ^ 26) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 5 0)] [] [].
Definition lt_ss0 : sstate := mkSS LP_J sr_atoms [lt_slots0] None lt_facts0.
Definition lt_ss1 : sstate := mkSS LP_J sr_atoms [lt_slots; lt_sh 0 0; lt_in; lt_rn; lt_rsh] None lt_facts1.
(* The input is used up: the plain run stops at beqz (0x8025c); its taken side runs to 0x80e54. *)
Definition lt_rx1 := Eval vm_compute in (sym_runN_pi boxb_tpi FUEL lt_ss0).
Definition lt_ssx1 : sstate := fst lt_rx1.
Definition lt_ssx2 : sstate := add_cond lt_ssx1 (mkAC BC_EQ (SOff 33 0) (SLit 0)).
Definition lt_rx2 := Eval vm_compute in (sym_run_toN_pi boxb_tpi FUEL LP_X lt_ssx2).
(* A byte is left: the token run stops at the store of mac's shadow byte (0x80290); with the shadow window open the
   plain run goes on to the call of __asan_memcpy. *)
Definition lt_r1 := Eval vm_compute in (sym_runN_pi_tok boxb_tpi boxb_tw LT_K lt_Bx lt_span [] FUEL lt_ss1).
Definition lt_ss2 : sstate :=
  let ss := sh_ss (fst lt_r1) in
  mkSS (ss_pc ss) (ss_regs ss) (list_upd (ss_mem ss) 1 lt_sh2) (ss_resv ss) (ss_facts ss).
Definition lt_r2 := Eval vm_compute in (sym_runN_pi boxb_tpi FUEL lt_ss2).
Definition lt_cs0 : list YP09.chunk := Eval vm_compute in
  (match nth_error (ss_mem (fst lt_r2)) 0 with Some rr => YP09.r_chunks rr | None => [] end).
Definition lt_cs1 : list YP09.chunk := Eval vm_compute in
  (match nth_error (ss_mem (fst lt_r2)) 1 with Some rr => YP09.r_chunks rr | None => [] end).

(* ---- small facts ---- *)
Lemma lt_aview_val : forall segs H (mem : word -> option byte) a v,
  aview segs H mem a = Some v -> 0 <= v < 256 -> val_mem segs (mrestrict H mem) a 1 v.
Proof.
intros segs H mem a v Ha Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
injection Ha as <-. f_equal.
unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma lt_nth_map : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma lt_div8 : forall a c, a mod 8 = 0 -> 0 <= c < 8 -> (a + c) / 8 = a / 8.
Proof.
intros a c Ha Hc. pose proof (Z.div_mod a 8 ltac:(lia)) as D.
symmetry. apply (Z.div_unique (a + c) 8 (a / 8) c); lia.
Qed.

Lemma lt_mod8 : forall a c, a mod 8 = 0 -> 0 <= c < 8 -> (a + c) mod 8 = c.
Proof.
intros a c Ha Hc. pose proof (Z.div_mod a 8 ltac:(lia)) as D.
symmetry. apply (Z.mod_unique (a + c) 8 (a / 8) c); lia.
Qed.

Lemma lt_den : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma lt_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity.
Qed.

Lemma lt_U_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof.
intros E n v c H Hv Hc. rewrite U_SOff, H, unsigned_lit_small by exact Hv. apply zcanon_id. unfold M64. lia.
Qed.

Lemma lt_LSH_entry_iter : forall j, (j < 52)%nat -> j <> 4%nat -> ~ (8 <= j < 44)%nat ->
  nth j LSH_entry 0 = nth j LSH_iter 0.
Proof.
intros j Hj H4 H8.
assert (Hc : (j < 4)%nat \/ (5 <= j < 8)%nat \/ (44 <= j < 52)%nat) by lia.
destruct Hc as [Hc | [Hc | Hc]].
- do 4 (destruct j as [|j]; [reflexivity|]). lia.
- do 5 (destruct j as [|j]; [lia|]). do 3 (destruct j as [|j]; [reflexivity|]). lia.
- do 44 (destruct j as [|j]; [lia|]). do 8 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma lt_LSH_iter_zero : forall j, (8 <= j < 44)%nat -> nth j LSH_iter 0 = 0.
Proof.
intros j Hj. unfold LSH_iter. rewrite app_nth2 by (cbn [length]; lia). cbn [length].
rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.

Lemma lt_cs1_zero : forall o, 8 <= o < 44 -> In (YP09.mkChunk o (CVal 1 (SLit 0))) lt_cs1.
Proof.
intros o Ho.
assert (Hj : exists j, (j < 36)%nat /\ o = 8 + Z.of_nat j) by (exists (Z.to_nat (o - 8)); lia).
destruct Hj as (j & Hj & ->).
do 36 (destruct j as [|j]; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; vm_compute; tauto |]). lia.
Qed.

Lemma lt_cs1_six : In (YP09.mkChunk 4 (CVal 1 (SLit 6))) lt_cs1.
Proof. vm_compute. tauto. Qed.

Lemma lt_cs1_f2 : forall o, 5 <= o < 8 -> In (YP09.mkChunk o (CVal 1 (SLit 242))) lt_cs1.
Proof.
intros o Ho. assert (Hc : o = 5 \/ o = 6 \/ o = 7) by lia.
destruct Hc as [-> | [-> | ->]]; vm_compute; tauto.
Qed.

Lemma lt_cs0_p : In (YP09.mkChunk 136 (CVal 8 (SOff 32 1))) lt_cs0.
Proof. vm_compute. tauto. Qed.

Lemma lt_cs0_n : In (YP09.mkChunk 144 (CVal 8 (SOff 33 (-1)))) lt_cs0.
Proof. vm_compute. tauto. Qed.

(* The runs, computed once (with the listing's instance, so no evar meets vm_compute). *)
Lemma lt_rx1_eq : sym_runN_pi (@pl_tpi boxb_listing PL_boxb) FUEL lt_ss0 = (lt_ssx1, snd lt_rx1).
Proof. vm_compute. reflexivity. Qed.
Lemma lt_rx2_eq : sym_run_toN_pi (@pl_tpi boxb_listing PL_boxb) FUEL LP_X lt_ssx2 = (fst lt_rx2, snd lt_rx2).
Proof. vm_compute. reflexivity. Qed.
Lemma lt_r1_eq : sym_runN_pi_tok (@pl_tpi boxb_listing PL_boxb) (@pl_tw boxb_listing PL_boxb) LT_K lt_Bx lt_span [] FUEL
  lt_ss1 = (fst lt_r1, PTS_stopped (SR_store (Some 22%nat) 4)).
Proof. vm_compute. reflexivity. Qed.
Lemma lt_r2_eq : sym_runN_pi (@pl_tpi boxb_listing PL_boxb) FUEL lt_ss2 = (fst lt_r2, PRS_call BB___asan_memcpy).
Proof. vm_compute. reflexivity. Qed.
Lemma lt_ss1_static : sh_static_ok LT_K lt_Bx lt_span [] (ss_facts lt_ss1) (ss_mem lt_ss1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lt_rx1_stop : pi_plain_stop (snd lt_rx1). Proof. vm_compute. exact I. Qed.
Lemma lt_rx2_stop : pi_plain_stop (snd lt_rx2). Proof. vm_compute. exact I. Qed.

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

(* A register the symbolic state keeps as an atom of the seat. *)
Lemma lt_reg_pi : forall E ss H ms (q : bv 5) n v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 -> ew E n = v -> getr (ms_regs ms) q = v.
Proof.
intros E ss H ms q n v HS Hq Hn. rewrite (st_ok_pi_restrict_reg H E ss ms q HS), Hq.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hn.
Qed.

Lemma lt_reg_st : forall E ss H ms (q : bv 5) n v,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 -> ew E n = v -> getr (ms_regs ms) q = v.
Proof.
intros E ss H ms q n v HS Hq Hn. rewrite (st_ok_restrict_reg SEGS H E ss ms q HS), Hq.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hn.
Qed.

Lemma lt_shape : forall pc (W : world SEGS) ms,
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS).
Proof.
intros pc W ms Hpc Hresv Hpend Hrom Hfregs Hfcsr.
destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
subst. reflexivity.
Qed.

Section d.
Variables (cx : lxcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model).
Variables (i pos : nat) (r fab : Z) (bs : list byte).
Hypothesis HB : lx_base B MT cx.
Hypothesis HJ : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
  [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HBD : lx_body cx fp LP_J W3 ms3 LSH_entry.
Hypothesis HBLK : lblk B cx ly3 S3 r.
Hypothesis HREG : lreg W3 ms3 r bs.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HCUR : lcur cx W3 ms3 pos.
Hypothesis HSL : lslots_loop cx fp W3 ms3 r fab.
Hypothesis G19 : getr (ms_regs ms3) 19 = w64 1.
Hypothesis G20 : getr (ms_regs ms3) 20 = w64 r.
Hypothesis G21 : getr (ms_regs ms3) 21 = w64 (lF cx fp + 64).

#[local] Notation sp0 := (lsp0 cx).
#[local] Notation sp1 := (lsp1 cx).
#[local] Notation FF := (lF cx fp).
#[local] Notation SHF := (lSH cx fp).
#[local] Notation PP := (lc_p cx + Z.of_nat pos).
#[local] Notation NN := (lc_n cx - Z.of_nat pos).
#[local] Notation OP := (bv_unsigned (nth pos (lc_pl cx) (Z_to_bv 8 0))).
#[local] Notation SR := (shadow_addr (r + 280)).
#[local] Notation EJ := (Eimg (Ereg (ms_regs ms3)
  [Z_to_bv 64 PP; Z_to_bv 64 NN; Z_to_bv 64 OP; Z_to_bv 64 (Boxreg.bx_n bs); Z_to_bv 64 SR])).

(* ---- the geometry of the cut ---- *)
Lemma lt_geo :
  sp0 mod 16 = 0 /\ alloc_ceiling + LX_STK <= sp0 <= 2 ^ 47 /\
  sp0 - 287 <= sp1 <= sp0 - 256 /\ sp1 mod 32 = 0 /\
  frame_addr ly3 LX_CID fp = FF /\ In (LX_CID, fp) (frames S3) /\
  4096 <= FF /\ FF + 512 <= alloc_ceiling /\ FF mod 64 = 0 /\ in_app FF 512 /\
  SHF = SHADOW_OFF + FF / 8 /\
  In (r, LX_REG) (ablocks B ly3 S3) /\
  r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ in_app r 288 /\
  (r + 288 <= FF \/ FF + 512 <= r).
Proof.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof HB as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly & _).
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly) as (_ & Efa & _).
assert (EF : frame_addr ly3 LX_CID fp = FF) by (unfold lF; apply Efa).
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR3 Hfin) as (HF0 & HF1 & HFa).
destruct (frame_al64 SEGS B _ _ _ _ _ _ _ HAR3 Hfin) as (HF64 & _).
rewrite EF, Hfb in *.
assert (Hin : In (r, LX_REG) (ablocks B ly3 S3)) by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hin) as (Hr16 & Hr4096 & Hrc & Hra & _).
change (req_size LX_REG) with 288 in *.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r LX_REG LX_CID fp HAR3 Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (req_size LX_REG) with 288 in Hsep. rewrite EF, Hfb in Hsep.
unfold LX_STK in *.
pose proof (Z.div_mod (lsp0 cx - 256) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (lsp0 cx - 256) 32 ltac:(lia)) as Hmp.
unfold lsp0 in *.
pose proof HFa as HFa'. pose proof Hra as Hra'. unfold in_app in HFa', Hra'.
repeat split;
  first [ exact EF | exact Hfin | exact HFa | exact Hin | exact Hra | lia | (unfold lsp1, lsp0; lia)
        | (unfold lsp1; rewrite Z.mul_comm, Z_mod_mult; reflexivity) | (unfold lSH, shadow_addr; reflexivity) ].
Qed.

(* ---- the input block, when a byte is left ---- *)
Lemma lt_inblk : NN <> 0 ->
  (pos < length (lc_pl cx))%nat /\ In (lc_p cx, lc_n cx) (ablocks B ly3 S3) /\
  4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling /\ in_app (lc_p cx) (lc_n cx) /\ 0 < lc_n cx < 2 ^ 26 /\
  (lc_p cx + lc_n cx <= r \/ r + 288 <= lc_p cx).
Proof.
intros HN.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof HB as (_ & _ & _ & Hn & _).
pose proof HJ as (HAR3 & _).
pose proof HCUR as (Hpos & _).
assert (Hlt : (pos < length (lc_pl cx))%nat) by (unfold lc_n in HN; lia).
assert (Hn0 : lc_n cx <> 0) by (unfold lc_n; lia).
destruct Hn as [[Hn _] | (Hnr & Hinc)]; [contradiction|].
assert (Hin : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hinc).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpc & Hpa & _).
assert (Hrq : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
rewrite Hrq in Hpc, Hpa.
apply in_split in Hinc as (l1 & l2 & El).
pose proof (sep_blocks_pos SEGS B LAWS _ _ _ _ _ (lc_p cx, lc_n cx) (r, LX_REG) l1 l2 [] HAR3) as Hsep.
unfold lblk in HBLK. rewrite HBLK, El, <- app_assoc in Hsep. cbn [app] in Hsep. specialize (Hsep eq_refl).
unfold zdisjoint, block_rng in Hsep. cbn [fst snd] in Hsep. rewrite Hrq in Hsep. change (req_size LX_REG) with 288 in Hsep.
pose proof Hpa as Hpa'. unfold in_app in Hpa'.
repeat split; first [assumption | lia].
Qed.

(* ---- the seats ---- *)
Lemma lt_E_facts :
  ew EJ 9 = Z_to_bv 64 sp1 /\ ew EJ 18 = Z_to_bv 64 SHADOW_OFF /\ ew EJ 19 = Z_to_bv 64 1 /\
  ew EJ 20 = Z_to_bv 64 r /\ ew EJ 22 = Z_to_bv 64 SHF /\
  ew EJ 32 = Z_to_bv 64 PP /\ ew EJ 33 = Z_to_bv 64 NN /\ ew EJ 34 = Z_to_bv 64 OP /\
  ew EJ 35 = Z_to_bv 64 (Boxreg.bx_n bs) /\ ew EJ 36 = Z_to_bv 64 SR.
Proof.
pose proof HBD as (_ & _ & _ & _ & _ & _ & (L2 & L8 & L9 & L3 & L4 & L18 & L22) & _).
split; [rewrite (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl); exact L9|].
split; [rewrite (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl); exact L18|].
split; [rewrite (ew_Eimg_Ereg_nat _ _ 19 19%bv eq_refl); exact G19|].
split; [rewrite (ew_Eimg_Ereg_nat _ _ 20 20%bv eq_refl); exact G20|].
split; [rewrite (ew_Eimg_Ereg_nat _ _ 22 22%bv eq_refl); exact L22|].
repeat split; reflexivity.
Qed.

Lemma lt_slots_base : forall E m o, m = mrestrict (w_H W3) (ms_mem ms3) ->
  ew E 9 = Z_to_bv 64 sp1 -> 0x88 <= o < 0x98 ->
  base_val E (Some 9%nat) = sp1 /\ writable_at SEGS m (sp1 + o).
Proof.
intros E m o -> E9 Ho.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof asan_consts as (C1 & _).
unfold LX_STK in *.
cbn [base_val]. rewrite E9, unsigned_lit_small by lia. split; [reflexivity|].
apply (apresent_writable SEGS). apply Hpres3. lia.
Qed.

Lemma lt_slots_ok : forall E m, m = mrestrict (w_H W3) (ms_mem ms3) ->
  ew E 9 = Z_to_bv 64 sp1 -> ew E 32 = Z_to_bv 64 PP -> ew E 33 = Z_to_bv 64 NN -> ew E 36 = Z_to_bv 64 SR ->
  0 <= PP < 2 ^ 64 -> 0 <= NN < 2 ^ 64 ->
  region_ok SEGS E m lt_slots.
Proof.
intros E m Hm E9 E32 E33 E36 HP HN.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & _ & _ & HF0 & HF1 & _ & _ & _ & _ & _ & Hr4096 & Hrc & _).
pose proof HCUR as (_ & S88 & S90).
pose proof HSL as (S08 & _ & _ & S38 & S40 & _).
pose proof asan_consts as (C1 & _).
unfold lslot, lview in S88, S90, S08, S38, S40.
unfold LX_STK in *.
unfold region_ok, lt_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (proj1 (lt_slots_base E m 0x88 Hm E9 ltac:(lia))).
split; [lia|]. split; [lia|]. split.
{ intros o Ho. exact (proj2 (lt_slots_base E m o Hm E9 Ho)). }
subst m.
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ _ 8 8 (SLit 3) 3); [reflexivity | zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S08).
- apply (chunk_ok_val SEGS E _ _ 56 8 (SLit 0) 0); [reflexivity | zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S38).
- apply (chunk_ok_val SEGS E _ _ 64 8 (SOff 36 0) SR); [exact (lt_den E 36 _ E36) | | zside |].
  + unfold shadow_addr, SHADOW_OFF. cbn [Z.of_N]. pose proof (Z.div_pos (r + 280) 8 ltac:(lia) ltac:(lia)).
    assert ((r + 280) / 8 <= r + 280) by (apply Z.div_le_upper_bound; lia). lia.
  + exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S40).
- apply (chunk_ok_val SEGS E _ _ 136 8 (SOff 32 0) PP); [exact (lt_den E 32 _ E32) | zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S88).
- apply (chunk_ok_val SEGS E _ _ 144 8 (SOff 33 0) NN); [exact (lt_den E 33 _ E33) | zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S90).
Qed.

Lemma lt_seat0 : NN = 0 -> st_ok_pi SEGS VAL EJ lt_ss0 (restrict (w_H W3) ms3).
Proof.
intros HN.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & _).
pose proof lt_E_facts as (E9 & _ & _ & _ & _ & _ & E33 & _).
pose proof HBD as (Hpc & Hresv & Hpend & Hrom & Hfregs & Hfcsr & _).
pose proof HCUR as (_ & _ & S90).
pose proof asan_consts as (C1 & _).
unfold lslot, lview in S90.
rewrite (lt_shape LP_J W3 ms3 Hpc Hresv Hpend Hrom Hfregs Hfcsr).
unfold lt_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold region_ok, lt_slots0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (proj1 (lt_slots_base EJ _ 0x88 eq_refl E9 ltac:(lia))).
  unfold LX_STK in *.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. exact (proj2 (lt_slots_base EJ _ o eq_refl E9 Ho)). }
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS EJ _ _ 144 8 (SOff 33 0) NN); [exact (lt_den EJ 33 _ E33) | rewrite HN; zside | zside |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S90).
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
- split; [|split; exact I].
  cbn [lt_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E33, HN, !unsigned_lit_small by (unfold LX_STK in *; lia).
  change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. unfold LT_SPLO, LX_STK in *.
  repeat split; try exact I; lia.
Qed.

Lemma lt_ER : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew EJ n = getr (ms_regs ms3) q.
Proof. intros n q Hn. exact (ew_Eimg_Ereg_nat (ms_regs ms3) _ n q Hn). Qed.

(* r->n, the word at r + 280, is bx_n bs (0 .. 5). *)
Lemma lt_rn_val : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (r + 280) 4 (Boxreg.bx_n bs).
Proof.
pose proof HINV as ((HL & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof HREG as HR. unfold lreg, lview in HR.
intros kk Hkk.
assert (HA : aview SEGS (w_H W3) (ms_mem ms3) (r + (280 + Z.of_nat kk)) =
  Some (bv_unsigned (nth (280 + kk) bs (Z_to_bv 8 0)))).
{ rewrite (HR (280 + Z.of_nat kk)) by (unfold LX_REG; lia).
  replace (Z.to_nat (280 + Z.of_nat kk)) with (280 + kk)%nat by lia. reflexivity. }
destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
replace (r + 280 + Z.of_nat kk) with (r + (280 + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
replace b with (nth (280 + kk) bs (Z_to_bv 8 0)) by (apply bv_eq; lia).
exact (fnd_n_bytes bs HL (proj1 HB1) kk Hkk).
Qed.

(* The shadow byte of r + 280 .. r + 287, a whole granule of the registry block, is 0. *)
Lemma lt_rsh_zero : aview SEGS (w_H W3) (ms_mem ms3) SR = Some 0.
Proof.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof lt_geo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hin & Hr16 & Hr4096 & Hrc & _).
pose proof HJ as (HAR3 & _).
pose proof (Z.div_mod r 16 ltac:(lia)) as Dr. rewrite Hr16, Z.add_0_r in Dr.
assert (H8 : (r + 280) mod 8 = 0) by (symmetry; apply (Z.mod_unique (r + 280) 8 (2 * (r / 16) + 35) 0); lia).
pose proof (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG (r + 280) 8 HAR3 Hin
  ltac:(lia) ltac:(change (req_size LX_REG) with 288; lia)) as HRA.
destruct (HRA (r + 287) ltac:(lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs.
replace (r + 287) with (r + 280 + 7) in Hs, Hok by lia.
rewrite (lt_div8 (r + 280) 7 H8 ltac:(lia)) in Hs.
unfold saddr_ok in Hok. rewrite (lt_mod8 (r + 280) 7 H8 ltac:(lia)) in Hok.
destruct Hok as [-> | Hok]; [|lia].
unfold shadow_addr. exact Hs.
Qed.

Lemma lt_seat1 : NN <> 0 -> st_ok_pi SEGS VAL EJ lt_ss1 (restrict (w_H W3) ms3).
Proof.
intros HN.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & EF & Hfin & HF0 & HF1 & HF64 & HFa & HSH & Hin & Hr16 & Hr4096
  & Hrc & Hra & Hsep).
pose proof (lt_inblk HN) as (Hlt & Hinp & Hp4096 & Hpc & Hpa & Hn26 & Hsepp).
pose proof lt_E_facts as (E9 & E18 & E19 & E20 & E22 & E32 & E33 & E34 & E35 & E36).
pose proof HBD as (Hpc0 & Hresv & Hpend & Hrom & Hfregs & Hfcsr & _ & _ & _ & _ & _ & _ & _ & Hgarr).
pose proof HINV as ((HL & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof HCUR as (Hpos & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HOP : 0 <= OP < 256)
  by (pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as R; change (bv_modulus 8) with 256 in R; exact R).
pose proof (Z.div_mod r 16 ltac:(lia)) as Dr. rewrite Hr16, Z.add_0_r in Dr.
pose proof (Z.div_mod FF 64 ltac:(lia)) as Df. rewrite HF64, Z.add_0_r in Df.
assert (DSR : (r + 280) / 8 = 2 * (r / 16) + 35) by (symmetry; apply (Z.div_unique (r + 280) 8 _ 0); lia).
assert (DF8 : FF / 8 = 8 * (FF / 64)) by (symmetry; apply (Z.div_unique FF 8 _ 0); lia).
assert (HSR : SR = SHADOW_OFF + (2 * (r / 16) + 35)) by (unfold shadow_addr; rewrite DSR; reflexivity).
rewrite DF8 in HSH.
unfold lc_n in *. unfold LX_STK, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
rewrite (lt_shape LP_J W3 ms3 Hpc0 Hresv Hpend Hrom Hfregs Hfcsr).
unfold lt_ss1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (lt_slots_ok EJ _ eq_refl E9 E32 E33 E36); unfold lc_n; lia|].
  apply Forall_cons.
  { unfold region_ok, lt_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E22, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | constructor]. }
  apply Forall_cons.
  { unfold region_ok, lt_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS EJ _ _ 0 1 (SOff 34 0) OP); [exact (lt_den EJ 34 _ E34) | zside | zside |].
    rewrite Z.add_0_r. destruct (Hgarr pos ltac:(rewrite length_map; lia)) as [Hv _].
    rewrite lt_nth_map in Hv. exact Hv. }
  apply Forall_cons.
  { unfold region_ok, lt_rn. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E20, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS EJ _ _ 280 4 (SOff 35 0) (Boxreg.bx_n bs)); [exact (lt_den EJ 35 _ E35) | zside | zside |].
    exact lt_rn_val. }
  apply Forall_cons; [|apply Forall_nil].
  { unfold region_ok, lt_rsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS EJ _ _ 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply lt_aview_val; [exact lt_rsh_zero | lia]. }
- apply pairwise_disjoint_of_extents.
  unfold lt_slots, lt_sh, lt_in, lt_rn, lt_rsh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E22, E32, E20, E36, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; exact I].
  cbn [lt_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E18, E19, E20, E32, E33, E34, E35, !unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold LT_SPLO, LT_SB. repeat split; try exact I; lia.
Qed.

(* ---- what the cut's memory facts keep ---- *)
Lemma lt_keep_common : forall ms' : machine_state,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 136 <= a < sp1 + 152) -> ~ (SHF + 4 <= a < SHF + 44) ->
     ~ (FF + 64 <= a < FF + 352) -> ~ (sp1 - 4096 <= a < sp1) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  lsaved cx W3 ms' /\ rdword (lview W3 ms') (FF + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W3 ms' 0x10 FF /\ lslot cx W3 ms' 0x18 FF /\ lslot cx W3 ms' 0x80 FF /\
  lslots_loop cx fp W3 ms' r fab /\ lreg W3 ms' r bs /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)).
Proof.
intros ms' KEEP.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & EF & Hfin & HF0 & HF1 & HF64 & HFa & HSH & Hin & Hr16 & Hr4096
  & Hrc & Hra & Hsep).
pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & (Hsv8 & Hsvj) & _ & Hflag & S10 & S18 & S80 & Hgarr).
pose proof HSL as (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
pose proof HB as (_ & _ & _ & Hn & _).
pose proof HJ as (HAR3 & _).
pose proof HREG as HR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod FF 64 ltac:(lia)) as Df. rewrite HF64, Z.add_0_r in Df.
assert (DF8 : FF / 8 = 8 * (FF / 64)) by (symmetry; apply (Z.div_unique FF 8 _ 0); lia).
rewrite DF8 in HSH.
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
unfold lslot, lsaved, lslots_loop, lreg in *. unfold lview in *.
unfold LX_STK, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
assert (KR : forall a v, (forall j, 0 <= j < 8 -> 0 <= a + j < 2 ^ 64 /\ ~ (lsp1 cx + 136 <= a + j < lsp1 cx + 152) /\
            ~ (SHF + 4 <= a + j < SHF + 44) /\ ~ (FF + 64 <= a + j < FF + 352) /\ ~ (lsp1 cx - 4096 <= a + j < lsp1 cx)) ->
          rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v).
{ intros a v Hr Hv.
  rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact Hv|].
  intros j Hj. destruct (Hr j Hj) as (H1 & H2 & H3 & H4 & H5). exact (KEEP _ H1 H2 H3 H4 H5). }
split; [split|].
{ apply KR; [intros j Hj; lia | exact Hsv8]. }
{ intros j Hj. apply KR; [intros jj Hjj; lia | exact (Hsvj j Hj)]. }
split; [apply KR; [intros j Hj; rewrite Hfb; lia | exact Hflag]|].
split; [apply KR; [intros j Hj; lia | exact S10]|].
split; [apply KR; [intros j Hj; lia | exact S18]|].
split; [apply KR; [intros j Hj; lia | exact S80]|].
split.
{ repeat split; (apply KR; [intros j Hj; lia | assumption]). }
split.
{ intros j Hj. unfold LX_REG in Hj. rewrite KEEP by lia. exact (HR j ltac:(unfold LX_REG; lia)). }
destruct Hn as [[Hn0 _] | (Hn & Hinc)].
- intros j Hj. rewrite length_map in Hj. unfold lc_n in Hn0. lia.
- assert (Hinp : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)).
  { unfold lblk in HBLK. rewrite HBLK. apply in_or_app. left. exact Hinc. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinp) as (_ & Hp4096 & Hpc & Hpa & _).
  assert (Hrq : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
  rewrite Hrq in Hpc, Hpa.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp HAR3 Hinp Hfin) as Hsepf.
  unfold zdisjoint in Hsepf. cbn [fst snd] in Hsepf. rewrite Hrq, EF, Hfb in Hsepf.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpa.
  intros j Hj. rewrite length_map in Hj. unfold lc_n in *.
  destruct (Hgarr j ltac:(rewrite length_map; exact Hj)) as [Hv Hb]. split; [|exact Hb].
  intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
  pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
  rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms') _ (KEEP (lc_p cx + Z.of_nat j) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia))).
  exact Hv0.
Qed.

(* ---- the landings ---- *)
Lemma lt_land_x : forall (regs' : bvmap 5 word) (mem' : word -> option byte) md',
  (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  getr regs' 2 = getr (ms_regs ms3) 2 -> getr regs' 8 = getr (ms_regs ms3) 8 -> getr regs' 9 = getr (ms_regs ms3) 9 ->
  getr regs' 3 = getr (ms_regs ms3) 3 -> getr regs' 4 = getr (ms_regs ms3) 4 ->
  getr regs' 18 = getr (ms_regs ms3) 18 -> getr regs' 22 = getr (ms_regs ms3) 22 -> getr regs' 20 = getr (ms_regs ms3) 20 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 136 <= a < sp1 + 152) ->
     aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  LI_X B MT cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + LP_X)) mem' (seg_rom SEGS)) md'.
Proof.
intros regs' mem' md' Hi Hk Hacc R2 R8 R9 R3 R4 R18 R22 R20 KEEPX.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & EF & Hfin & HF0 & HF1 & HF64 & HFa & HSH & _).
pose proof HBD as (_ & _ & _ & _ & _ & _ & (L2 & L8 & L9 & L3 & L4 & L18 & L22) & _ & Hsh & _).
pose proof (lh_mtl _ _ HY) as MTL.
pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as M48. pose proof (mo_free_nonneg MT MTL) as MF.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod FF 64 ltac:(lia)) as Df. rewrite HF64, Z.add_0_r in Df.
assert (DF8 : FF / 8 = 8 * (FF / 64)) by (symmetry; apply (Z.div_unique FF 8 _ 0); lia).
rewrite DF8 in HSH. unfold LX_STK, SHADOW_OFF in *.
destruct (lt_keep_common (mkst regs' (Z_to_bv 64 (BASE + LP_X)) mem' (seg_rom SEGS))) as (KS & KF & K10 & K18 & K80 & _ & _ & KG).
{ intros a Ha H1 _ _ _. exact (KEEPX a Ha H1). }
exists r. split.
{ unfold lx_body.
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold lregs. cbn [ms_regs mkst]. rewrite R2, R8, R9, R3, R4, R18, R22. repeat split; assumption. }
  split; [exact KS|].
  split.
  { intros j Hj. change (length LSH_entry) with 52%nat in Hj. unfold lview. cbn [ms_mem mkst].
    rewrite KEEPX; [exact (Hsh j ltac:(change (length LSH_entry) with 52%nat; exact Hj)) | lia | lia]. }
  split; [exact KF|]. split; [exact K10|]. split; [exact K18|]. split; [exact K80|]. exact KG. }
split; [lia|].
split; [unfold LX_AI in *; nia|].
split; [exact HBLK|].
cbn [ms_regs mkst]. rewrite R20. exact G20.
Qed.

Lemma lt_land_t : forall (regs4 : bvmap 5 word) (mem4 : word -> option byte) md4,
  NN <> 0 -> (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  Boxreg.bx_fabric bs = fab ->
  getr regs4 2 = w64 sp1 -> getr regs4 8 = w64 sp0 -> getr regs4 9 = w64 sp1 ->
  getr regs4 3 = getr (lc_regs cx) 3 -> getr regs4 4 = getr (lc_regs cx) 4 ->
  getr regs4 18 = w64 SHADOW_OFF -> getr regs4 22 = w64 SHF ->
  getr regs4 19 = w64 1 -> getr regs4 20 = w64 r -> getr regs4 21 = w64 (FF + 64) -> getr regs4 23 = w64 OP ->
  getr regs4 24 = w64 (Z.of_nat i) -> getr regs4 26 = w64 (Boxreg.bx_n bs) -> getr regs4 27 = w64 fab ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 136 <= a < sp1 + 152) -> ~ (SHF + 4 <= a < SHF + 44) ->
     ~ (FF + 64 <= a < FF + 352) -> ~ (sp1 - 4096 <= a < sp1) ->
     aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall j, 0 <= j < 288 -> aview SEGS (w_H W3) mem4 (FF + 64 + j) = aview SEGS (w_H W3) (ms_mem ms3) (r + j)) ->
  rdword (aview SEGS (w_H W3) mem4) (sp1 + 136) = Some (PP + 1) ->
  rdword (aview SEGS (w_H W3) mem4) (sp1 + 144) = Some (NN - 1) ->
  aview SEGS (w_H W3) mem4 (SHF + 4) = Some 6 ->
  (forall o, 5 <= o < 8 -> aview SEGS (w_H W3) mem4 (SHF + o) = Some 242) ->
  (forall o, 8 <= o < 44 -> aview SEGS (w_H W3) mem4 (SHF + o) = Some 0) ->
  LI_T B MT (Z.land OP 3) i cx fp k acc ly3 S3 W3 (mkst regs4 (Z_to_bv 64 (BASE + LP_T)) mem4 (seg_rom SEGS)) md4.
Proof.
intros regs4 mem4 md4 HN Hi Hk Hacc HFAB R2 R8 R9 R3 R4 R18 R22 R19 R20 R21 R23 R24 R26 R27 KEEP PREV CUR1 CUR2 SH4 SH567 SH0.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & EF & Hfin & HF0 & HF1 & HF64 & HFa & HSH & Hin & Hr16 & Hr4096
  & Hrc & Hra & Hsep).
pose proof (lt_inblk HN) as (Hlt & Hinp & Hp4096 & Hpc & Hpa & Hn26 & Hsepp).
pose proof HBD as (_ & _ & _ & _ & _ & _ & (L2 & L8 & L9 & L3 & L4 & L18 & L22) & _ & Hsh & _).
pose proof HCUR as (Hpos & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (Z.div_mod FF 64 ltac:(lia)) as Df. rewrite HF64, Z.add_0_r in Df.
assert (DF8 : FF / 8 = 8 * (FF / 64)) by (symmetry; apply (Z.div_unique FF 8 _ 0); lia).
rewrite DF8 in HSH. unfold LX_STK in *.
destruct (lt_keep_common (mkst regs4 (Z_to_bv 64 (BASE + LP_T)) mem4 (seg_rom SEGS)) KEEP)
  as (KS & KF & K10 & K18 & K80 & KL & KR & KG).
exists pos, r, fab, OP, bs.
split.
{ unfold lx_body.
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold lregs. cbn [ms_regs mkst]. rewrite R2, R8, R9, R3, R4, R18, R22.
    rewrite <- L3, <- L4. repeat split; reflexivity. }
  split; [exact KS|].
  split.
  { intros j Hj. change (length LSH_iter) with 52%nat in Hj. unfold lview. cbn [ms_mem mkst].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    destruct (Nat.eq_dec j 4) as [-> | H4].
    { change (nth 4 LSH_iter 0) with 6. exact SH4. }
    destruct (le_lt_dec 8 j) as [H8 | H8];
      [destruct (lt_dec j 44) as [H44 | H44] | destruct (le_lt_dec 5 j) as [H5 | H5]].
    - rewrite lt_LSH_iter_zero by lia. apply SH0. lia.
    - rewrite <- (lt_LSH_entry_iter j) by lia.
      rewrite KEEP by lia. exact (Hsh j ltac:(change (length LSH_entry) with 52%nat; lia)).
    - assert (Hc : j = 5%nat \/ j = 6%nat \/ j = 7%nat) by lia.
      destruct Hc as [-> | [-> | ->]]; [exact (SH567 5 ltac:(lia)) | exact (SH567 6 ltac:(lia)) | exact (SH567 7 ltac:(lia))].
    - rewrite <- (lt_LSH_entry_iter j) by lia.
      rewrite KEEP by lia. exact (Hsh j ltac:(change (length LSH_entry) with 52%nat; lia)). }
  split; [exact KF|]. split; [exact K10|]. split; [exact K18|]. split; [exact K80|]. exact KG. }
split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact KR|].
split; [exact HINV|]. split; [exact HFAB|].
split.
{ intros j Hj. unfold lview. cbn [ms_mem mkst]. rewrite PREV by (unfold LX_REG in Hj; lia). exact (HREG j Hj). }
split; [exact Hlt|]. split; [reflexivity|]. split; [reflexivity|].
split.
{ unfold lcur, lslot, lview. cbn [ms_mem mkst]. rewrite Nat2Z.inj_succ.
  split; [lia|]. split.
  - replace (lc_p cx + Z.succ (Z.of_nat pos)) with (PP + 1) by lia. exact CUR1.
  - replace (lc_n cx - Z.succ (Z.of_nat pos)) with (NN - 1) by lia. exact CUR2. }
split; [exact KL|].
cbn [ms_regs mkst].
split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R23|].
split; [exact R24|]. split; [exact R26 | exact R27].
Qed.

(* ---- the walks ---- *)
(* The input is used up: ld a1, in.n; beqz a1 to 0x80e54. *)
Lemma lt_walk_x : NN = 0 -> (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  mo_le MT (lc_S cx) S3 acc ->
  forall POST : lxcx -> world SEGS -> config -> Prop,
  lx_from B MT POST (LI_X B MT) -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros HN Hi Hk Hacc HMO POST HX.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & _).
pose proof lt_E_facts as (E9 & _ & _ & _ & _ & _ & E33 & _).
pose proof (lt_seat0 HN) as HS.
assert (HEI : img_env VAL A_LIM EJ) by apply Eimg_env.
assert (ER : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew EJ n = getr (ms_regs ms3) q) by exact lt_ER.
pose proof asan_consts as (C1 & _).
set (E := EJ) in *. clearbody E.
rewrite HN in E33.
unfold LX_STK in *.
eapply (SRr_run_pi_AJ B LAWS W3 FUEL E lt_ss0 lt_ssx1 (snd lt_rx1) ms3 LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx)
  (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 md3 k (POST cx) HEI HS lt_rx1_eq lt_rx1_stop HJ).
- change (ss_mem lt_ss0) with [lt_slots0].
  apply (awr_ok_cons_stack_off E lt_slots0 _ LX_STK (lsp0 cx) [] _ _ ly3 _ 9%nat (lsp1 cx - lsp0 cx) eq_refl);
    [rewrite E9, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo lt_slots0]; unfold LX_STK; lia
    | cbn [YP09.r_whi lt_slots0]; lia |].
  apply awr_ok_nil.
- intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1.
  apply (paj_branch W3 E lt_ssx1 ms1 _ _ BC_EQ (SOff 33 0) (SLit 0) HS1); intros Hc HS1'.
  2: { exfalso. rewrite branch_eq_U, (U_atom E 33 0 E33 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc. discriminate Hc. }
  change (st_ok_pi SEGS VAL E lt_ssx2 (restrict (w_H W3) ms1)) in HS1'.
  eapply (SRr_run_to_pi_AJ B LAWS W3 FUEL LP_X E lt_ssx2 (fst lt_rx2) (snd lt_rx2) ms1 LX_STK (lsp0 cx) []
    (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k (POST cx)
    HEI HS1' lt_rx2_eq lt_rx2_stop HJ1).
  + lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fpp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fpp b0 bc ly own) end.
    eapply (awr_ok_cons_stack_off E _ _ LX_STK (lsp0 cx) [] _ _ ly3 _ 9%nat (lsp1 cx - lsp0 cx));
      [reflexivity | rewrite E9, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; unfold LX_STK; lia
      | cbn [YP09.r_whi]; lia |].
    apply awr_ok_nil.
  + intros ms2 mat2 HS2 HJ2 HF2 HFr2 HG2.
    assert (KEEPX : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx + 136 <= a < lsp1 cx + 152) ->
      aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hw. transitivity (aview SEGS (w_H W3) (ms_mem ms1) a).
      - apply (kept_of_frame E (ss_mem lt_ssx2) (w_H W3) (ms_mem ms1) (ms_mem ms2)
          (fun x => lsp1 cx + 136 <= x < lsp1 cx + 152) HFr2); [|exact Ha|exact Hw].
        intros bb wlo whi aa Hwin Hr. vm_compute in Hwin.
        destruct Hwin as [Hw' | []]; injection Hw' as <- <- <-; cbn [base_val] in Hr.
        rewrite E9, unsigned_lit_small in Hr by lia. lia.
      - apply (kept_of_frame E (ss_mem lt_ss0) (w_H W3) (ms_mem ms3) (ms_mem ms1)
          (fun x => lsp1 cx + 136 <= x < lsp1 cx + 152) HFr1); [|exact Ha|exact Hw].
        intros bb wlo whi aa Hwin Hr. vm_compute in Hwin.
        destruct Hwin as [Hw' | []]; injection Hw' as <- <- <-; cbn [base_val] in Hr.
        rewrite E9, unsigned_lit_small in Hr by lia. lia. }
    assert (RK : forall (q : bv 5) n, sr_get (ss_regs (fst lt_rx2)) q = SOff n 0 -> Z.of_nat n = bv_unsigned q ->
      getr (ms_regs ms2) q = getr (ms_regs ms3) q).
    { intros q n Hq Hn. exact (lt_reg_pi E (fst lt_rx2) (w_H W3) ms2 q n _ HS2 Hq (ER n q Hn)). }
    assert (Q2 : getr (ms_regs ms2) 2 = getr (ms_regs ms3) 2) by (apply (RK 2%bv 2%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q8 : getr (ms_regs ms2) 8 = getr (ms_regs ms3) 8) by (apply (RK 8%bv 8%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q9 : getr (ms_regs ms2) 9 = getr (ms_regs ms3) 9) by (apply (RK 9%bv 9%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q3 : getr (ms_regs ms2) 3 = getr (ms_regs ms3) 3) by (apply (RK 3%bv 3%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q4 : getr (ms_regs ms2) 4 = getr (ms_regs ms3) 4) by (apply (RK 4%bv 4%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q18 : getr (ms_regs ms2) 18 = getr (ms_regs ms3) 18) by (apply (RK 18%bv 18%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q22 : getr (ms_regs ms2) 22 = getr (ms_regs ms3) 22) by (apply (RK 22%bv 22%nat); first [vm_compute; reflexivity | reflexivity]).
    assert (Q20 : getr (ms_regs ms2) 20 = getr (ms_regs ms3) 20) by (apply (RK 20%bv 20%nat); first [vm_compute; reflexivity | reflexivity]).
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS2 eq_refl).
    replace (ss_pc (fst lt_rx2)) with LP_X by (vm_compute; reflexivity).
    apply (HX cx fp k acc ly3 S3 W3 (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + LP_X)) (ms_mem ms2) (seg_rom SEGS)) _
      HB HJ2 HFR HMO).
    apply lt_land_x; assumption.
Qed.

(* A byte is left: the op byte, the shadow stores, r->n, and __asan_memcpy (prev, r, 288). *)
Lemma lt_walk_t : NN <> 0 -> (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i -> acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  mo_le MT (lc_S cx) S3 acc -> getr (ms_regs ms3) 24 = w64 (Z.of_nat i) -> getr (ms_regs ms3) 27 = w64 fab ->
  Boxreg.bx_fabric bs = fab ->
  forall POST : lxcx -> world SEGS -> config -> Prop,
  (forall c, 0 <= c < 4 -> lx_from B MT POST (LI_T B MT c i)) -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros HN Hi Hk Hacc HMO G24 G27 HFAB POST HT.
pose proof (lh_laws _ _ HY) as LAWS.
pose proof pa_segs_low as Hsegs.
pose proof lt_geo as (Hal16 & Hsp0 & Hsp1 & H32 & EF & Hfin & HF0 & HF1 & HF64 & HFa & HSH & Hin & Hr16 & Hr4096
  & Hrc & Hra & Hsep).
pose proof (lt_inblk HN) as (Hlt & Hinp & Hp4096 & Hpc & Hpa & Hn26 & Hsepp).
pose proof lt_E_facts as (E9 & E18 & E19 & E20 & E22 & E32 & E33 & E34 & E35 & E36).
pose proof HBD as (_ & _ & _ & _ & _ & _ & (L2 & L8 & L9 & L3 & L4 & L18 & L22) & _).
pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof HCUR as (Hpos & _).
pose proof HREG as HR. unfold lreg, lview in HR.
pose proof (lt_seat1 HN) as HS.
assert (HEI : img_env VAL A_LIM EJ) by apply Eimg_env.
assert (ER : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew EJ n = getr (ms_regs ms3) q) by exact lt_ER.
assert (SHOK : sh_ok SEGS lt_Bx [] EJ (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose proof HJ as (HAR3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HOP : 0 <= OP < 256)
  by (pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as R; change (bv_modulus 8) with 256 in R; exact R).
pose proof (Z.div_mod FF 64 ltac:(lia)) as Df. rewrite HF64, Z.add_0_r in Df.
assert (DF8 : FF / 8 = 8 * (FF / 64)) by (symmetry; apply (Z.div_unique FF 8 _ 0); lia).
rewrite DF8 in HSH.
pose proof (Z.div_mod (lsp1 cx) 32 ltac:(lia)) as Ds1. rewrite H32, Z.add_0_r in Ds1.
pose proof (Z.div_mod (lsp0 cx) 16 ltac:(lia)) as Ds0. rewrite Hal16, Z.add_0_r in Ds0.
assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
set (E := EJ) in *. clearbody E.
unfold lc_n in *. unfold LX_STK, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
(* 0x80258 .. 0x8028c: the token run, up to the store of mac's shadow byte *)
eapply (paj_run B LAWS W3 FUEL E LT_K lt_Bx lt_span [] lt_ss1 (fst lt_r1) (PTS_stopped (SR_store (Some 22%nat) 4))
  ms3 LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 md3 k (POST cx)
  ltac:(unfold A_LIM, LT_K; lia) HEI HS SHOK lt_ss1_static lt_r1_eq HJ).
(* the shadow check of the input byte: the input block's shadow *)
{ change (sh_obls (fst lt_r1)) with [mkOB (SOff 32 0) 1].
  apply Forall_cons; [|apply Forall_nil]. unfold ob_holds. cbn [ob_x ob_n].
  rewrite <- (aview_rd_of SEGS). unfold lt_Bx.
  rewrite (U_atom E 18 _ E18) by lia. rewrite (U_atom E 32 _ E32) by lia.
  apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (lc_p cx) (Z.of_nat (length (lc_pl cx))) _ 1
    HAR3 Hinp); [lia|].
  unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (lc_pl cx))) 0); lia. }
{ change (ss_mem lt_ss1) with [lt_slots; lt_sh 0 0; lt_in; lt_rn; lt_rsh].
  apply (awr_ok_cons_stack_off E lt_slots _ LX_STK (lsp0 cx) [] _ _ ly3 _ 9%nat (lsp1 cx - lsp0 cx) eq_refl);
    [rewrite E9, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo lt_slots]; unfold LX_STK; lia
    | cbn [YP09.r_whi lt_slots]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi lt_sh lt_in lt_rn lt_rsh]; lia|]).
  apply awr_ok_nil. }
intros ws ms1 mat1 Hlen1 HEI1 HS1 SHOK1 HJ1 HFo1 HFr1 HG1.
change (st_ok_pi SEGS VAL (extK E LT_K ws) (sh_ss (fst lt_r1)) (restrict (w_H W3) ms1)) in HS1.
pose proof (env_agree_extK E LT_K ws) as (OLD1 & _).
set (E1 := extK E LT_K ws) in *. clearbody E1.
assert (F9 : ew E1 9 = Z_to_bv 64 (lsp1 cx)) by (rewrite OLD1 by (unfold LT_K; lia); exact E9).
assert (F20 : ew E1 20 = Z_to_bv 64 r) by (rewrite OLD1 by (unfold LT_K; lia); exact E20).
assert (F22 : ew E1 22 = Z_to_bv 64 SHF) by (rewrite OLD1 by (unfold LT_K; lia); exact E22).
assert (F32 : ew E1 32 = Z_to_bv 64 PP) by (rewrite OLD1 by (unfold LT_K; lia); exact E32).
assert (F33 : ew E1 33 = Z_to_bv 64 NN) by (rewrite OLD1 by (unfold LT_K; lia); exact E33).
assert (F34 : ew E1 34 = Z_to_bv 64 OP) by (rewrite OLD1 by (unfold LT_K; lia); exact E34).
assert (F35 : ew E1 35 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite OLD1 by (unfold LT_K; lia); exact E35).
assert (FR : forall n (q : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned q -> ew E1 n = getr (ms_regs ms3) q)
  by (intros n q Hn Hq; rewrite OLD1 by (unfold LT_K; lia); exact (ER n q Hq)).
assert (B9 : bv_unsigned (ew E1 9) = lsp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (B22 : bv_unsigned (ew E1 22) = SHF) by (rewrite F22; apply unsigned_lit_small; lia).
(* outside the cursor's window the token run kept every byte *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx + 136 <= a < lsp1 cx + 152) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw1.
  apply (kept_of_frame E (ss_mem lt_ss1) (w_H W3) (ms_mem ms3) (ms_mem ms1)
    (fun x => lsp1 cx + 136 <= x < lsp1 cx + 152) HFr1); [|exact Ha|exact Hw1].
  intros bb wlo whi aa Hwin Hr. vm_compute in Hwin.
  destruct Hwin as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-; cbn [base_val] in Hr;
    first [rewrite E9, unsigned_lit_small in Hr by lia; lia | lia]. }
(* the shadow window [4, 44) of the frame's shadow bytes, with the bytes 5 .. 7 (0xf2) it does not store *)
pose proof HJ1 as (HAR1 & _).
pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & _ & HshJ & _).
assert (HR1w : region_ok SEGS E1 (ms_mem (restrict (w_H W3) ms1)) lt_sh2).
{ unfold region_ok, lt_sh2.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
  rewrite B22. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS).
    destruct (al_frames _ _ LAWS _ _ _ _ _ LX_CID fp HAR1 Hfin) as (_ & _ & _ & Hshp).
    rewrite EF, Hfb in Hshp. exact (proj1 (Hshp o ltac:(change (512 / 8) with 64; lia))). }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val SEGS E1 _ _ 5 1 (SLit 242) 242); [reflexivity | zside | zside |].
    apply lt_aview_val; [|lia]. rewrite KEEP1 by lia. exact (HshJ 5%nat ltac:(cbn; lia)).
  - apply (chunk_ok_val SEGS E1 _ _ 6 1 (SLit 242) 242); [reflexivity | zside | zside |].
    apply lt_aview_val; [|lia]. rewrite KEEP1 by lia. exact (HshJ 6%nat ltac:(cbn; lia)).
  - apply (chunk_ok_val SEGS E1 _ _ 7 1 (SLit 242) 242); [reflexivity | zside | zside |].
    apply lt_aview_val; [|lia]. rewrite KEEP1 by lia. exact (HshJ 7%nat ltac:(cbn; lia)). }
pose proof (ast_ok_pi_set_region E1 (sh_ss (fst lt_r1)) _ 1 (lt_sh 0 0) lt_sh2 HS1
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) HR1w) as HS2.
change (st_ok_pi SEGS VAL E1 lt_ss2 (restrict (w_H W3) ms1)) in HS2.
(* 0x80290 .. 0x80348: the plain run, up to the call of __asan_memcpy *)
eapply (SRr_run_pi_AJ_call B LAWS W3 FUEL E1 lt_ss2 (fst lt_r2) BB___asan_memcpy ms1 LX_STK (lsp0 cx) []
  (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k (POST cx)
  HEI1 HS2 lt_r2_eq HJ1).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fpp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fpp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off E1 _ _ LX_STK (lsp0 cx) [] _ _ ly3 _ 9%nat (lsp1 cx - lsp0 cx));
    [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo]; unfold LX_STK; lia | cbn [YP09.r_whi]; lia |].
  eapply (YCbq.awr_ok_cons_gen E1 _ _ LX_STK (lsp0 cx) [] _ _ ly3 _ 22%nat SHF); [reflexivity | exact B22 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. change (512 / 8) with 64. unfold lSH in Ha. lia. }
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]).
  apply awr_ok_nil. }
intros ms2 mat2 HS3 HJ2 HF2 HFr2 HG2.
pose proof HJ2 as (HAR2 & _).
(* what the runs wrote: the cursor, mac's and prev's shadow bytes *)
pose proof (st_ok_region_nth E1 (setpc (fst lt_r2) (SIGMA BB___asan_memcpy)) (restrict (w_H W3) ms2) 0 (YP09.mkRegion (Some 9%nat) 8 152 136 152 lt_cs0) HS3
  ltac:(vm_compute; reflexivity)) as HR0.
pose proof (st_ok_region_nth E1 (setpc (fst lt_r2) (SIGMA BB___asan_memcpy)) (restrict (w_H W3) ms2) 1 (YP09.mkRegion (Some 22%nat) 0 64 4 44 lt_cs1) HS3
  ltac:(vm_compute; reflexivity)) as HRs.
cbn [ms_mem restrict] in HR0, HRs.
assert (CUR1 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (lsp1 cx + 136) = Some (PP + 1)).
{ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms2)); [|lia].
  exact (field_of_region E1 _ 9 _ lt_cs0 8 152 136 152 136 8 (SOff 32 1) (PP + 1) HR0 B9 lt_cs0_p
    (lt_den_off E1 32 PP 1 F32 ltac:(lia)) ltac:(zside) ltac:(zside)). }
assert (CUR2 : rdword (aview SEGS (w_H W3) (ms_mem ms2)) (lsp1 cx + 144) = Some (NN - 1)).
{ apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms2)); [|unfold lc_n; lia].
  replace (NN - 1) with (NN + -1) by lia.
  exact (field_of_region E1 _ 9 _ lt_cs0 8 152 136 152 144 8 (SOff 33 (-1)) (NN + -1) HR0 B9 lt_cs0_n
    (lt_den_off E1 33 NN (-1) F33 ltac:(unfold lc_n; lia)) ltac:(unfold lc_n; zside) ltac:(zside)). }
assert (SH4 : aview SEGS (w_H W3) (ms_mem ms2) (SHF + 4) = Some 6).
{ apply (aview_of_val_mem1 SEGS); [|lia].
  exact (field_of_region E1 _ 22 _ lt_cs1 0 64 4 44 4 1 (SLit 6) 6 HRs B22 lt_cs1_six eq_refl ltac:(zside) ltac:(zside)). }
assert (SH567 : forall o, 5 <= o < 8 -> aview SEGS (w_H W3) (ms_mem ms2) (SHF + o) = Some 242).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  exact (field_of_region E1 _ 22 _ lt_cs1 0 64 4 44 o 1 (SLit 242) 242 HRs B22 (lt_cs1_f2 o Ho) eq_refl
    ltac:(zside) ltac:(zside)). }
assert (SH0 : forall o, 8 <= o < 44 -> aview SEGS (w_H W3) (ms_mem ms2) (SHF + o) = Some 0).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  exact (field_of_region E1 _ 22 _ lt_cs1 0 64 4 44 o 1 (SLit 0) 0 HRs B22 (lt_cs1_zero o Ho) eq_refl
    ltac:(zside) ltac:(zside)). }
(* outside the runs' windows every byte is the cut's *)
assert (KEEP12 : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx + 136 <= a < lsp1 cx + 152) -> ~ (SHF + 4 <= a < SHF + 44) ->
  aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw1 Hw2. transitivity (aview SEGS (w_H W3) (ms_mem ms1) a).
  - apply (kept_of_frame E1 (ss_mem lt_ss2) (w_H W3) (ms_mem ms1) (ms_mem ms2)
      (fun x => (lsp1 cx + 136 <= x < lsp1 cx + 152) \/ (SHF + 4 <= x < SHF + 44)) HFr2); [|exact Ha|tauto].
    intros bb wlo whi aa Hwin Hr. vm_compute in Hwin.
    destruct Hwin as [Hw | [Hw | [Hw | [Hw | [Hw | []]]]]]; injection Hw as <- <- <-; cbn [base_val] in Hr;
      first [rewrite B9 in Hr; left; lia | rewrite B22 in Hr; right; lia | lia].
  - exact (KEEP1 a Ha Hw1). }
(* the registers at the call *)
assert (RQ : forall (q : bv 5) n, sr_get (ss_regs (setpc (fst lt_r2) (SIGMA BB___asan_memcpy))) q = SOff n 0 ->
  forall v, ew E1 n = v -> getr (ms_regs ms2) q = v).
{ intros q n Hq v Hv. exact (lt_reg_st E1 _ (w_H W3) ms2 q n v HS3 Hq Hv). }
assert (C2r : getr (ms_regs ms2) 2 = w64 (lsp1 cx))
  by (apply (RQ 2%bv 2%nat ltac:(vm_compute; reflexivity)); rewrite (FR 2%nat 2%bv) by first [lia | reflexivity]; exact L2).
assert (C8r : getr (ms_regs ms2) 8 = w64 (lsp0 cx))
  by (apply (RQ 8%bv 8%nat ltac:(vm_compute; reflexivity)); rewrite (FR 8%nat 8%bv) by first [lia | reflexivity]; exact L8).
assert (C9r : getr (ms_regs ms2) 9 = w64 (lsp1 cx))
  by (apply (RQ 9%bv 9%nat ltac:(vm_compute; reflexivity)); rewrite (FR 9%nat 9%bv) by first [lia | reflexivity]; exact L9).
assert (C3r : getr (ms_regs ms2) 3 = getr (lc_regs cx) 3)
  by (apply (RQ 3%bv 3%nat ltac:(vm_compute; reflexivity)); rewrite (FR 3%nat 3%bv) by first [lia | reflexivity]; exact L3).
assert (C4r : getr (ms_regs ms2) 4 = getr (lc_regs cx) 4)
  by (apply (RQ 4%bv 4%nat ltac:(vm_compute; reflexivity)); rewrite (FR 4%nat 4%bv) by first [lia | reflexivity]; exact L4).
assert (C18r : getr (ms_regs ms2) 18 = w64 SHADOW_OFF)
  by (apply (RQ 18%bv 18%nat ltac:(vm_compute; reflexivity)); rewrite (FR 18%nat 18%bv) by first [lia | reflexivity]; exact L18).
assert (C22r : getr (ms_regs ms2) 22 = w64 SHF)
  by (apply (RQ 22%bv 22%nat ltac:(vm_compute; reflexivity)); rewrite (FR 22%nat 22%bv) by first [lia | reflexivity]; exact L22).
assert (C19r : getr (ms_regs ms2) 19 = w64 1)
  by (apply (RQ 19%bv 19%nat ltac:(vm_compute; reflexivity)); rewrite (FR 19%nat 19%bv) by first [lia | reflexivity]; exact G19).
assert (C20r : getr (ms_regs ms2) 20 = w64 r)
  by (apply (RQ 20%bv 20%nat ltac:(vm_compute; reflexivity)); rewrite (FR 20%nat 20%bv) by first [lia | reflexivity]; exact G20).
assert (C21r : getr (ms_regs ms2) 21 = w64 (FF + 64))
  by (apply (RQ 21%bv 21%nat ltac:(vm_compute; reflexivity)); rewrite (FR 21%nat 21%bv) by first [lia | reflexivity]; exact G21).
assert (C24r : getr (ms_regs ms2) 24 = w64 (Z.of_nat i))
  by (apply (RQ 24%bv 24%nat ltac:(vm_compute; reflexivity)); rewrite (FR 24%nat 24%bv) by first [lia | reflexivity]; exact G24).
assert (C27r : getr (ms_regs ms2) 27 = w64 fab)
  by (apply (RQ 27%bv 27%nat ltac:(vm_compute; reflexivity)); rewrite (FR 27%nat 27%bv) by first [lia | reflexivity]; exact G27).
assert (C23r : getr (ms_regs ms2) 23 = w64 OP) by (apply (RQ 23%bv 34%nat ltac:(vm_compute; reflexivity)); exact F34).
assert (C26r : getr (ms_regs ms2) 26 = w64 (Boxreg.bx_n bs))
  by (apply (RQ 26%bv 35%nat ltac:(vm_compute; reflexivity)); exact F35).
assert (C10r : getr (ms_regs ms2) 10 = w64 (FF + 64))
  by (apply (RQ 10%bv 21%nat ltac:(vm_compute; reflexivity)); rewrite (FR 21%nat 21%bv) by first [lia | reflexivity]; exact G21).
assert (C11r : getr (ms_regs ms2) 11 = w64 r) by (apply (RQ 11%bv 20%nat ltac:(vm_compute; reflexivity)); exact F20).
assert (C12r : getr (ms_regs ms2) 12 = w64 288).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E1 _ ms2 12%bv HS3).
  lazymatch goal with |- sv_denot _ (sr_get ?l ?q) = _ =>
    let v := eval vm_compute in (sr_get l q) in change (sr_get l q) with v end.
  reflexivity. }
assert (C1r : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + 928)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E1 _ ms2 1%bv HS3).
  lazymatch goal with |- sv_denot _ (sr_get ?l ?q) = _ =>
    let v := eval vm_compute in (sr_get l q) in change (sr_get l q) with v end.
  exact (codeptr_val E1 928 HEI1). }
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS3 eq_refl). cbn [ss_pc setpc].
(* __asan_memcpy (F + 64, r, 288): the destination is prev, in the call's own frame; the source the registry *)
eapply SRr_bind.
{ apply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BB___asan_memcpy) (lh_memcpy _ _ HY) W3 (ms_regs ms2) (ms_mem ms2)
    LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k
    (FF + 64) r 288 (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + 928)) HJ2).
  - exact C10r.
  - exact C11r.
  - exact C12r.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite C2r. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - replace (lsp1 cx - lsp0 cx) with ((2 * (lsp1 cx / 32) - lsp0 cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ESTACK, LX_STK. lia.
  - rewrite C3r. exact Hgp.
  - rewrite C4r. exact Htp.
  - exact C1r.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    right; right; right. exists LX_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. lia.
  - exact (amem_range_sub_app FF 512 (FF + 64) 288 HFa HF1 ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    assert (Hx1 : 8 * (FF / 64) + 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
    assert (Hx2 : x / 8 < 8 * (FF / 64) + 44) by (apply Z.div_lt_upper_bound; lia).
    unfold SHADOW_OFF. replace (2147450880 + x / 8) with (SHF + (x / 8 - 8 * (FF / 64))) by lia.
    apply SH0. lia.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms2) _ LX_CID fp _ _ HAR2 Hfin);
      rewrite ?EF, ?Hfb; lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite KEEP12 by lia.
        pose proof (HR (a - r) ltac:(unfold LX_REG; lia)) as Ha'. replace (r + (a - r)) with a in Ha' by lia.
        rewrite Ha'. discriminate.
      - unfold spZ. rewrite C2r. unfold w64, ESTACK. rewrite unsigned_lit_small by lia. lia. }
    split; [lia|].
    split; [exact (amem_range_of_block SEGS B LAWS _ _ _ _ _ r LX_REG r 288 HAR2 Hin ltac:(lia)
              ltac:(change (req_size LX_REG) with 288; lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ r LX_REG r 288 HAR2 Hin ltac:(lia)
              ltac:(change (req_size LX_REG) with 288; lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ r LX_REG r 288 HAR2 Hin ltac:(lia)
              ltac:(change (req_size LX_REG) with 288; lia) ltac:(lia)). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
assert (Hc : 0 <= Z.land OP 3 < 4).
{ change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  pose proof (Z.mod_pos_bound OP 4 ltac:(lia)). lia. }
apply (HT (Z.land OP 3) Hc cx fp k acc ly3 S3 W3 (mkst regs4 (Z_to_bv 64 (BASE + LP_T)) mem4 (seg_rom SEGS)) md4
  HB HJ4 HFR HMO).
assert (PR : forall q, acallee_saved q -> getr regs4 (Z_to_bv 5 q) = getr (ms_regs ms2) (Z_to_bv 5 q)) by exact HP4.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (FF + 64 <= a < FF + 352) -> ~ (lsp1 cx - 4096 <= a < lsp1 cx) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms2) a).
{ intros a Ha H1 H2. apply Hfr4; [exact Ha | lia | unfold ESTACK; lia]. }
apply lt_land_t.
- exact HN.
- exact Hi.
- exact Hk.
- exact Hacc.
- exact HFAB.
- etransitivity; [exact (PR 2 ltac:(unfold acallee_saved; lia)) | exact C2r].
- etransitivity; [exact (PR 8 ltac:(unfold acallee_saved; lia)) | exact C8r].
- etransitivity; [exact (PR 9 ltac:(unfold acallee_saved; lia)) | exact C9r].
- etransitivity; [exact (PR 3 ltac:(unfold acallee_saved; lia)) | exact C3r].
- etransitivity; [exact (PR 4 ltac:(unfold acallee_saved; lia)) | exact C4r].
- etransitivity; [exact (PR 18 ltac:(unfold acallee_saved; lia)) | exact C18r].
- etransitivity; [exact (PR 22 ltac:(unfold acallee_saved; lia)) | exact C22r].
- etransitivity; [exact (PR 19 ltac:(unfold acallee_saved; lia)) | exact C19r].
- etransitivity; [exact (PR 20 ltac:(unfold acallee_saved; lia)) | exact C20r].
- etransitivity; [exact (PR 21 ltac:(unfold acallee_saved; lia)) | exact C21r].
- etransitivity; [exact (PR 23 ltac:(unfold acallee_saved; lia)) | exact C23r].
- etransitivity; [exact (PR 24 ltac:(unfold acallee_saved; lia)) | exact C24r].
- etransitivity; [exact (PR 26 ltac:(unfold acallee_saved; lia)) | exact C26r].
- etransitivity; [exact (PR 27 ltac:(unfold acallee_saved; lia)) | exact C27r].
- intros a Ha H1 H2 H3 H4. rewrite KM by lia. apply KEEP12; lia.
- intros j Hj. rewrite (Heff j Hj). apply KEEP12; lia.
- rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms2)) (aview SEGS (w_H W3) mem4)); [exact CUR1|].
  intros j Hj. apply KM; lia.
- rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms2)) (aview SEGS (w_H W3) mem4)); [exact CUR2|].
  intros j Hj. apply KM; lia.
- rewrite KM by lia. exact SH4.
- intros o Ho. rewrite KM by lia. apply SH567. exact Ho.
- intros o Ho. rewrite KM by lia. apply SH0. exact Ho.
Qed.

End d.

Theorem lx_top : forall (POST : lxcx -> world SEGS -> config -> Prop) i,
  lx_from B MT POST (LI_X B MT) -> (forall c, 0 <= c < 4 -> lx_from B MT POST (LI_T B MT c i)) ->
  lx_from B MT POST (LI_J B MT i).
Proof.
intros POST i HX HT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (pos & r & fab & bs & HBD & Hi & Hk & Hacc & HBLK & HREG & HINV & HFAB & HCUR & HSL
  & G19 & G20 & G21 & G24 & G27).
destruct (Z.eq_dec (lc_n cx - Z.of_nat pos) 0) as [HN | HN].
- eapply lt_walk_x; eassumption.
- eapply lt_walk_t; eassumption.
Qed.

End a.
