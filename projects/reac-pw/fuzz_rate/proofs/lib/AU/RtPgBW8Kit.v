(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the
   save-slot region, regs_ok_override / ck_regs_ok / ck_lit / ck_atom, ck_kept_run, awr_stk / kwr_stk, the run /
   keep / leaf chain, ck_wx / ck_segs_low) and proofs/reac-pw/fuzz_role/lib/A/RPgRefuse.v at 77f59d02b01 (the .got
   word and shadow-offset cell regions with base None and their al_const proofs) for reac-pw/fuzz_headamp's image A
   (fuzz_headamp.asan): the common plumbing of the walks of headamp's check functions against lib/A/HPgCSpec.v's
   hd_check_*_specX. What is new against role's files: the .got word 0x9c370 and the cell 0xa4db8 of this image;
   the entry state takes data regions and pointer facts as arguments (role's check functions read no memory); the
   shadow entries of the token engine (YCbn.v) for the checked pointer ranges, proved from the contracts'
   range_addressable and hd_app_rng premises (hc_shent); the leaf closes HPgCSpec's hd_post (its ra clause and its
   stack window T_check_STK = 32 around the 16-byte save slot); AR's laws come from the kernel theorem
   YG0q.AR_laws_ok, not a Section hypothesis. Everything here is generic over the segments and over the .got word
   and the cell (hc_entry_at, hc_app_apart_at, hc_prelude_with); the last block is image A's instance, and
   lib/AU/HPgChkBaseU.v is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgChkBase.v, with its module paths and module names changed; 263 of its 318 lines of code are new or changed and 308 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW5Kit.v and
   proofs/reac-pw/fuzz_role/lib/A/RPgW5Seg.v at ada533759b23 for reac-pw/fuzz_rate image A: the code table, the
   shadow band and the engine helpers are rate's (the prefix w5_ becomes rw8_, the image is images.Asan instead of
   a lib/A/Img0 module, RPgMem's rm_ lemmas become RtPgMem's rtm_); the post of a block is RtPgSteps.rts_post
   instead of a local copy; the five run statements of the piece are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW8Kit.v at 8f1d7a0a9084 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the pcs, the code tables and the registers are image
   B's; the prefix rw8_ becomes rbw8_, RtPgMem's rtm_ becomes RtPgMemB's rtmb_ and RtPgSteps' rts_ becomes RtPgStepsB's
   rtsb_; the frame for locals is the class-4 frame (1024 bytes) with the pod in e62 at F + 0x210; image B calls
   pod_write_ent where image A inlines it, so runs A and B become the one run P to the call, and the run statements
   and the piece's block statement (rbw8_core_stmt, A's rw8_core_stmt of lib/A/RtPgW8Core.v) are restated. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the shared part of the
   walk piece "write + record" of LLVMFuzzerTestOneInput (0x8076c), J 0x820dc -> C 0x813a0 / CL 0x824c0
   (pod.h:428-433: the capacity guard, the call pod_write_ent(pp, e62), the record copy and the pod loop's latch).
   Proves no function (kind: segment lemma): statement text and engine helpers only.

   WHAT THE PIECE DOES (listing of image B; the model is Pod/Model.enc_pod and Pod/Layout.pp_image_ent).
     0x820dc .. 0x820e8  the check of the 8-byte load of pp->len (its shadow address is the cell R+0x170)
     0x820ec             s9 := t1 (what is left of the input)
     0x820f0 .. 0x820fc  the capacity guard `bltu 0x4000, len + 112` -> 0x82484 (dead: len <= 5440)
     0x82100 .. 0x82108  a0 := pp (R+0x168), a1 := s6 = &e62 (F + 0x210), `jal pod_write_ent` (ra = 0x8210c)
     0x8210c .. 0x82114  a0 := `first` (R+0x160), a1 := k (R+0x178), `beqz a0` -> 0x82178
     0x82118 .. 0x82170  (first set) the check of pp->n_ent (pp + 0x4d14, shadow address R+0xf8 + K), the UBSan
                         trap `addiw a2,a0,1; blt a2,a0`, the store check, n_ent := n_ent + 1, the trap tests
                         n_ent >= 33 and ~(pp + 0x4014) < 104 n_ent, __asan_memcpy(&pp->ent[n_ent], e62, 104)
                         with ra = 0x82174
     0x82174 .. 0x821c0  a1 := k (only after the copy); e62 goes out of scope (13 shadow bytes := 0xf8 at
                         s3 + 66 .. 78), s8 := -8, k += 1, `bne a1,a0` to the pod loop's head C 0x813a0
                         (k + 1 <> cnt, R+0x140) or `j` to the params Struct's close CL 0x824c0.
   FOUR RUNS. The two calls cut the piece into four engine runs:
     rbw8_runP_stmt  J 0x820dc -> pod_write_ent 0x83cc4     1 check (pp->len), the capacity guard
     rbw8_runC1_stmt 0x8210c   -> __asan_memcpy 0x518b8     2 checks (pp->n_ent), 3 trap branches, `first` set
     rbw8_runC0_stmt 0x8210c   -> 0x82178                   no check, `first` clear
     rbw8_runD_stmt  0x82174 / 0x82178 -> C / CL             no check (plain engine: the frame's shadow stores)
   pod_write_ent's own contract is lib/AU/PweSpec.v's pod_write_ent_specX at 0x83cc4 (through RtPgStepsB's
   rtsb_pwe_at); the copy's is the kernel's aintrin_realizes at __asan_memcpy 0x518b8. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec RtPgMemB RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition RBW8_J : Z := 0x820dc.       (* the piece's start (RtPgSegB.RSB_J) *)
Definition RBW8_PWE : Z := 0x83cc4.     (* pod_write_ent (RtPgStepsB.PWE_ENT) *)
Definition RBW8_RA1 : Z := 0x8210c.     (* after pod_write_ent (RtPgStepsB.PWE_RA_COUNT) *)
Definition RBW8_CPY : Z := 0x518b8.     (* __asan_memcpy (RtPgStepsB.RTSB_MEMCPY) *)
Definition RBW8_RA2 : Z := 0x82174.     (* after the record copy *)
Definition RBW8_T0 : Z := 0x82178.      (* the scope stores, entered directly when `first` is clear *)
Definition RBW8_C : Z := 0x813a0.       (* the pod loop's head (RtPgSegB.RSB_C) *)
Definition RBW8_CL : Z := 0x824c0.      (* the params Struct's close (RtPgSegB.RSB_CL) *)
Lemma rbw8_pcs : RBW8_PWE = PWE_ENT /\ RBW8_RA1 = PWE_RA_COUNT /\ RBW8_CPY = RTSB_MEMCPY.
Proof. repeat split; reflexivity. Qed.

(* ======================================== the code ========================================
   [0x820dc, 0x821c4) is the piece and the branch that leaves it; [0x82228, 0x82250) are the two slow blocks of
   the n_ent checks and [0x832cc, 0x832d4) / [0x83344, 0x83354) the out-of-line report entries of the three checks,
   which the token engine decodes to tell one from the other. *)
Definition rbw8_tbl : ctable :=
  build_table rsegs 0x820dc 58 (build_table rsegs 0x82228 10 (build_table rsegs 0x832cc 2
  (build_table rsegs 0x83344 4 TEmpty))).
Lemma rbw8_tbl_ok : table_ok rsegs rbw8_tbl.
Proof.
unfold rbw8_tbl. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.
(* the plain-engine table of the last run (the scope stores and the latch) *)
Definition rbw8_tblD : ctable := build_table rsegs 0x82174 20 TEmpty.
Lemma rbw8_tblD_ok : table_ok rsegs rbw8_tblD.
Proof. apply build_table_ok0. lia. Qed.
Lemma rbw8_wx : wx_segs_nowrap rsegs.
Proof. exact rtsb_wx. Qed.
Lemma rbw8_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof. exact rtsb_segs_low. Qed.
Lemma rbw8_ret1 : YK0s.ret_ok (Z_to_bv 64 RBW8_RA1).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma rbw8_ret2 : YK0s.ret_ok (Z_to_bv 64 RBW8_RA2).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* ======================================== the engine's vocabulary ======================================== *)
(* env slot 32 is the runtime's shadow offset K; the band of shadow addresses the tokens may name *)
Definition RBW8_SB : Z := 0x7fff8000.
Definition rbw8_Bx : sv := SOff 32 0.
Definition rbw8_Bspan : Z * Z := (RBW8_SB, RBW8_SB + 2 ^ 44 - 1).
Lemma rbw8_SB_K : RBW8_SB = SHADOW_OFF.
Proof. reflexivity. Qed.
(* the shadow address of the atom n plus c, as the code forms it: `srli x,y,3; add x,x,s4` *)
Definition rbw8_shr (n : nat) (c : Z) : sv := SAlu ALU_SRL (SOff n c) (SLit 3).
Definition rbw8_sh (n : nat) (c : Z) : sv := SAlu ALU_ADD (rbw8_shr n c) rbw8_Bx.
(* the entry registers: the atoms of Ereg with the overrides ov (register, the value the start state gives it) *)
Definition rbw8_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.

(* ======================================== engine helpers ======================================== *)
Section h. Context {fx : YK11.FPState}.
Lemma rbw8_regs_ok_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma rbw8_regs_ok : forall E regs extra (ov : list (bv 5 * sv)), E = Ereg regs extra ->
Forall (fun p => fst p <> 0%bv /\ sv_denot E (snd p) = getr regs (fst p)) ov ->
regs_ok E (rbw8_sr ov) regs.
Proof.
intros E regs extra ov -> Hov. unfold rbw8_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
apply IH. apply rbw8_regs_ok_override; assumption. }
apply G. apply regs_ok_Ereg.
Qed.
(* the engine's entry state, over an environment named by its equation *)
Lemma rbw8_entry : forall pc sr regs extra E (rs : smem) (G : facts) mem, E = Ereg regs extra ->
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok rsegs E mem) rs -> pairwise_disjoint E rs ->
facts_ok E G -> st_ok rsegs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)).
Proof. intros pc sr regs extra E rs G mem -> Hr Hw Hrs Hpd HG. apply entry_st_ok_full; assumption. Qed.
Lemma rbw8_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. subst r. apply H. reflexivity. Qed.
(* a value the start state names: an atom plus an offset, read as an unsigned word *)
Lemma rbw8_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. apply (U_atom_off E n v c Hn Hv Hc).
Qed.
Lemma rbw8_den_shr : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 ->
sv_denot E (rbw8_shr n c) = w64 (Z.shiftr (v + c) 3).
Proof.
intros E n v c Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold rbw8_shr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n v c Hn) by lia. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). reflexivity.
Qed.
Lemma rbw8_den_sh : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 RBW8_SB ->
0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 -> sv_denot E (rbw8_sh n c) = w64 (shadow_addr (v + c)).
Proof.
intros E n v c Hn HK Hv Hc. rewrite denot_lit_U. unfold w64. f_equal. unfold rbw8_sh, rbw8_shr, rbw8_Bx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn) by lia. rewrite (U_atom E 32 RBW8_SB HK) by (unfold RBW8_SB; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
unfold shadow_addr. rewrite <- rbw8_SB_K. rewrite zcanon_id by (unfold M64, RBW8_SB; lia). lia.
Qed.
(* the byte a one-byte chunk holds *)
Lemma rbw8_mbyte_chunk1 : forall E (m : word -> option byte) base off e,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 1 e)) ->
mbyte rsegs m (base + off) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E m base off e H. destruct (H 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.
(* a register outside clob whose final symbolic value is its start value holds its start value *)
Lemma rbw8_regs_kept : forall E E' K sr0 srf (regs regs2 : bvmap 5 word) (clob : list (bv 5)),
regs_ok E sr0 regs -> regs_ok E' srf regs2 -> env_agree K E E' ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob ||
  (sv_eqb (sr_get srf r) (sr_get sr0 r) && sv_atoms_lt K (sr_get sr0 r))) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.
Proof.
intros E E' K sr0 srf regs regs2 clob H0 Hf HA Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply andb_prop in Hq as [Hq Hat]. apply sv_eqb_eq in Hq.
  rewrite (Hf r), Hq, (H0 r). apply (sv_denot_agree K E E' _ HA Hat).
Qed.
(* the value of a register in a final symbolic state, over atoms the run's environment keeps *)
Lemma rbw8_reg_val : forall E Ef K sr (regs : bvmap 5 word) (r : bv 5) v,
regs_ok Ef sr regs -> env_agree K E Ef -> sr_get sr r = v -> sv_atoms_lt K v = true ->
getr regs r = sv_denot E v.
Proof. intros E Ef K sr regs r v HR HA Hv Hl. rewrite (HR r), Hv. apply (sv_denot_agree K E Ef v HA Hl). Qed.
(* the bytes a run keeps: every address outside the write windows of its start regions *)
Lemma rbw8_kept_run : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.
Lemma rbw8_zc : forall x q r, 0 <= r < 18446744073709551616 -> x = 18446744073709551616 * q + r -> zcanon x = r.
Proof.
intros x q r Hr Hx. unfold zcanon, M64. change (2 ^ 64) with 18446744073709551616.
symmetry. apply (Z.mod_unique_pos x 18446744073709551616 q r Hr Hx).
Qed.
Lemma rbw8_val_kept : forall H mem H' mem' a n v,
val_mem rsegs (mrestrict H mem) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' mem' x = aview rsegs H mem x) ->
val_mem rsegs (mrestrict H' mem') a n v.
Proof.
intros H mem H' mem' a n v V K. apply rtmb_val_of_bytes. eapply rtmb_bytes_kept; [apply rtmb_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.
Lemma rbw8_pres : forall (regsT regs2 : bvmap 5 word) (r : bv 5),
aregs_preserved regsT regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regsT r.
Proof. intros regsT regs2 r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
End h.

(* ======================================== facts the runs re-derive ======================================== *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma rbw8_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
(* a shadow entry over bytes of a live block: they are marked usable, and they lie outside the shadow band *)
Lemma rbw8_shent_blk : forall ly S W mem md p m E n lo hi a0,
AR rsegs B ly S W mem md -> In (p, m) (ablocks B ly S) ->
ew E n = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> ew E 32 = Z_to_bv 64 RBW8_SB ->
0 <= lo <= hi -> p <= a0 + lo -> a0 + hi <= p + req_size m ->
shent_ok rsegs rbw8_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros ly S W mem md p m E n lo hi a0 HAR Hin Hn Ha0 HK Hlh Hlo Hhi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (_ & Hp4096 & Hpc & Happ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (UB : U E rbw8_Bx = SHADOW_OFF)
  by (unfold rbw8_Bx; rewrite (U_atom E 32 RBW8_SB HK) by (unfold RBW8_SB; lia); reflexivity).
assert (UN : U E (SOff n 0) = a0) by (apply U_atom; assumption).
split; cbn [she_m she_lo she_hi].
- rewrite UB, UN. rewrite <- aview_rd_of.
  apply (range_addressable_of_block rsegs B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite UN in Ha. rewrite UB.
  rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold in_app in Happ. rewrite C3 in *. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
End f.

(* ======================================== the geometry of a run ========================================
   The real frame R (`addi sp,sp,-0x220`, R = s1 = sp), the frame for locals F (the class-4 side-stack frame at
   pos, 1024 bytes) and the callers' window, as RtPgSegB's rsb_pre fixes them. *)
(* the frame's shadow patterns of the piece: e62 in scope at J (RtPgSegB.rsb_PJ), every object out at C / CL
   (RtPgSegB.rsb_P0) *)
Definition rbw8_PJ : list Z := rtmb_sh false false false false false true false.
Definition rbw8_P0 : list Z := rtmb_sh false false false false false false false.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Definition rbw8_geo (STK sp0 : Z) (own : list (Z * Z)) (lyc : alayout) (R F pos : Z) : Prop :=
R mod 16 = 0 /\ sp0 - STK <= R - T_SEG_STK /\ R + 0x220 <= sp0 /\ kHighMemBeg <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\ in_app F 1024 /\ F mod 32 = 0.

(* the registers each run may change *)
Definition rbw8_clobP : list (bv 5) := [1; 10; 11; 25]%bv.
Definition rbw8_clobC : list (bv 5) := [1; 10; 11; 12]%bv.
Definition rbw8_clobC0 : list (bv 5) := [10; 11]%bv.
Definition rbw8_clobD : list (bv 5) := [10; 11; 24]%bv.
(* the registers the whole piece may change: the runs' and every caller-saved one (the two calls) *)
Definition rbw8_clobJ : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%bv.

(* ---------------- run P: J 0x820dc -> pod_write_ent 0x83cc4 ----------------
   sp = s1 = R, s2 = &pp->len, s4 = K, s6 = &e62; the cells R+0x168 (pp) and R+0x170 (the shadow address of
   &pp->len) are read; the capacity guard is not taken (len <= 5440). *)
Definition rbw8_runP_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp F pos len : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rbw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 18 = w64 (pp + 0x4000) ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
0 <= len <= 5440 ->
SRr rsegs W (cfg_at rsegs RBW8_J regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RBW8_PWE rbw8_clobP (fun _ => False)
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 RBW8_RA1 /\ getr regs2 10 = w64 pp /\ getr regs2 11 = w64 (F + 0x210) /\
     getr regs2 25 = getr regs 6)).

(* ---------------- run C: 0x8210c -> the record copy (first set) or the scope stores (first clear) ----------
   Set: the cells R+0xe8 (&pp->ent[0]), R+0xf0 (its complement, the trap test's bound), R+0xf8 ((&pp->n_ent) >> 3),
   R+0x138 (&pp->n_ent), R+0x160 (`first` = 1) and R+0x178 (k, read and dropped) are read; pp->n_ent = kk is read,
   checked twice and written kk + 1; a0 / a1 / a2 are the copy's arguments. *)
Definition rbw8_runC1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp F pos kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rbw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 20 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (pp + 0x4014) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (Z.lnot (pp + 0x4014) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160) 8 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x178) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk ->
0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs RBW8_RA1 regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RBW8_CPY rbw8_clobC
  (fun a => pp + 0x4d14 <= a < pp + 0x4d18)
  (fun W2 regs2 mem2 =>
     getr regs2 1 = w64 RBW8_RA2 /\ getr regs2 10 = w64 (pp + 0x4014 + 104 * kk) /\
     getr regs2 11 = w64 (F + 0x210) /\ getr regs2 12 = w64 104 /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 (kk + 1))).
(* clear: `beqz a0` is taken with a1 = k *)
Definition rbw8_runC0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R F pos kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rbw8_geo STK sp0 own lyc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160) 8 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x178) 8 kk ->
0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs RBW8_RA1 regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RBW8_T0 rbw8_clobC0 (fun _ => False)
  (fun W2 regs2 mem2 => getr regs2 11 = w64 kk)).

(* ---------------- run D: the scope stores and the latch, to C or to CL ----------------
   s3 = the frame's shadow base; the cells R+0x140 (cnt) and R+0x178 (k) are read; a1 = k when entered at T0. *)
Definition rbw8_runD_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R F pos cnt kk pc0 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
rbw8_geo STK sp0 own lyc R F pos ->
(pc0 = RBW8_RA2 \/ pc0 = RBW8_T0) -> (pc0 = RBW8_T0 -> getr regs 11 = w64 kk) ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 cnt ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x178) 8 kk ->
1 <= cnt <= 32 -> 0 <= kk <= 31 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (if kk + 1 =? cnt then RBW8_CL else RBW8_C) rbw8_clobD
  (fun a => shadow_addr F + 66 <= a < shadow_addr F + 79)
  (fun W2 regs2 mem2 =>
     getr regs2 11 = w64 (kk + 1) /\ getr regs2 24 = w64 (-8) /\
     (forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 66 + i) = Some 0xf8))).

(* ======================================== the piece as one block ========================================
   The piece's start state as explicit facts (lib/AU/RtPgBW8.v turns RtPgSegB's cut J into them) and its end state
   as the bytes the model asks for; lib/AU/RtPgBW8Core.v proves it from the four runs and the two contracts. The
   write set is the pod's bytes in the first block and its length word (pod_write_ent's pwe_E), the record and the
   count word when `first` is set, the thirteen shadow bytes of e62, and the callees' stack (pod_write_ent's
   T_pwe_STK = 48 + ESTACK below R, which holds __asan_memcpy's ESTACK). *)
Definition rbw8_core_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R pp F pos len cnt kk fsv : Z) (ed : ent),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> st_nev S + k <= EV_MAX ->
rbw8_geo STK sp0 own lyc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 18 = w64 (pp + 0x4000) -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 22 = w64 (F + 0x210) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (pp + 0x4014) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (Z.lnot (pp + 0x4014) mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 cnt ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160) 8 fsv ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x170) 8 (shadow_addr (pp + 0x4000)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x178) 8 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 len ->
(fsv = 1 -> val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 kk) ->
rtmb_bytes rsegs (w_H W) memc (F + 0x210) (ent_mem ed) ->
rt_fsh rsegs (w_H W) memc F rbw8_PJ ->
ent_wf ed -> 32 <= len -> len + 56 <= 5440 -> len mod 8 = 0 ->
1 <= cnt <= 32 -> 0 <= kk <= 31 -> (fsv = 0 \/ fsv = 1) ->
SRr rsegs W (cfg_at rsegs RBW8_J regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
  (if kk + 1 =? cnt then RBW8_CL else RBW8_C) rbw8_clobJ
  (fun a => (pp + len <= a < pp + len + pwe_len ed) \/
            (pp + 0x4000 <= a < pp + 0x4008) \/
            (fsv = 1 /\ pp + 0x4d14 <= a < pp + 0x4d18) \/
            (fsv = 1 /\ pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104) \/
            (shadow_addr F + 66 <= a < shadow_addr F + 79) \/
            (R - T_pwe_STK <= a < R))
  (fun W2 regs2 mem2 =>
     getr regs2 11 = w64 (kk + 1) /\ getr regs2 24 = w64 (-8) /\ getr regs2 25 = getr regs 6 /\
     val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (len + pwe_len ed) /\
     rtmb_bytes rsegs (w_H W2) mem2 (pp + len) (enc_pod ed) /\
     (fsv = 1 -> rtmb_bytes rsegs (w_H W2) mem2 (pp + 0x4014 + 104 * kk) (ent_mem ed) /\
                 val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d14) 4 (kk + 1)) /\
     rt_fsh rsegs (w_H W2) mem2 F rbw8_P0)).
End st.
