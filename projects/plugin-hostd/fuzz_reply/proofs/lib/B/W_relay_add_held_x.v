(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the HELD segment of the image-B walk of fuzz_reply's relay_add over a
   generic allocator relation ARx in the ROOM form: pb_rb_held_x : rb_held_stmt B PST ARx MT RP G RG CTX
   (lib/B/W_relay_add_cut_x.v), from the cut RBH (0x82b3c, back from pthread_mutex_lock) to the cut RBA (0x82b90, the
   append).  Converted from the AR segment lib/B/W_relay_add_held.v (pb_ra_held, a working branch
   22c3862876d; removed from this tree by KF-COUNT #4), whose machine-code account holds
   unchanged (below), by route (b) (CONVERSION.md sha256 1015972e02a9; internal record): AR_laws -> AR_laws_x with the laws
   al_* -> alx_*, ajournal_gx -> ajournal_gx_x (Hp after S, Hp' after S'), paj_run_x / paj_run_to_x ->
   paj_run_x_x / paj_run_to_x_x with the token tactics paj_run_tok_x / paj_run_to_tok_x (W_kit_x.v), and the realloc
   rule -> the room-form arealloc_cf_rule_c_x (W_journal_x.v), called as image A's room walk calls it (the relay_add
   walk of W_relay_add.v (sha256 db38e2e41e5d; internal record), its realloc call with the room).  The AR-free helpers of the donor are copied unchanged.
   - A FRESH symbolic state is seated at 0x82b3c from RBH (hd_seat): the registers are atoms, the three globals are
     read-only regions at their object atoms (g_nsrc A_OBJ 4, g_capsrc A_OBJ 13, g_src A_OBJ 5) whose values are the
     extra atoms 32 (|es|, in [0, 3]), 33 (the capacity, 0 or 16) and 34 (the table T).
   - 0x82b3c-0x82b50: the auipc images s3 / s5 / s4 and the loads, to `bne a0,a1` 0x82b50.
     bne TAKEN (|es| <> the capacity): the table exists (T = 0 forces es = [] and the capacity 0), so ra_rel's
     right arm holds; one step to 0x82b90 and RBA with T1 = T, the memory unchanged; no allocator call, so RBA's room
     rp_RM RP S kr is the entry's budget (ra_cost MT_rk T = 0 at T <> 0).
     bne NOT TAKEN (|es| = the capacity): T = 0 and es = [] (T <> 0 gives the capacity 16 = |es| < 4); `beqz a0`
     0x82b54 is taken (its other arm, which holds the int32 doubling guard and the TRAP 0x82b60, is refuted at the
     branch: a0 = |es| = 0); s6 = 16, a0 = g_src = 0, a1 = 56 * 16 = 896, realloc 0x82b80 (AREALLOC on the inner
     journal of the ajournal_gx_x, hd_realloc_x).  The rule's room premises: the live counts cnt_ok at the call's
     state (the entry's: the lock left the allocator state as it was) from the entry's cnt_ok_pk at ra_peak 0 by
     cnt_ok_pk_mono; the stack room below the call from the journal (aj_stack_room_x, o = -64, ASTACK + 64 <= RA_STK);
     the budget rp_RM RP S (2 + kr) from the entry's (ra_cost MT_rk 0 = 2).  The rule's post rp_RM RP S2 kr is RBA's
     room.  Back at 0x82b84 with a0 = the new block (atom 44, >= 4096 by the rule, 16-aligned by the blocks law), so
     `beqz a0` (the error path 0x82c44 to fprintf) is decided NOT TAKEN by the runner; the stores `sd a0,500(s4)` /
     `sw s6,576(s5)` go through the kept auipc registers into two fresh writable regions at A_HI 30 / A_HI 29
     (offsets 500 / 576); RBA with T1 = the block.
   TRAP EDGES in HELD: 0x82b60 (`lui a1,0x40000; addw a1,a0,a1; bltz a1 -> unimp`, the int32 doubling guard) lies
   on the `beqz a0` arm with a0 <> 0, refuted at 0x82b54 from a0 = |es| = 0.  The error path 0x82b84 -> 0x82c44
   (unlock, fprintf (stderr), return -1) is refuted by the runner from atom 44's fact.  Callees: realloc only.
   Section hypotheses: the donor's, converted (only those this segment uses), plus HPST (the image is off PST: the
   ROM-view lemma ajournal_gx_rom_view_x asks the ROM bytes off PST; the text of lib/B/W_op_add.v Section x; trivial at
   PST = []). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_kit_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_cut W_relay_add_cut_x.
(* route R: SRrG / wle' (YA0nH) and relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag the donor's proofs run with, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* a run whose regions have no write window: every write-window obligation is vacuous *)
#[local] Ltac hd_nowr :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); exfalso;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia | ]);
destruct Hin.
(* ... and leaves the memory as it was (B_rr_scan.v rrs_mem) *)
#[local] Ltac hd_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
(* name the machine state HS is about (W_gse_loop.v gsl_cur) *)
#[local] Ltac hd_cur HS nm :=
lazymatch type of HS with context [restrict _ ?m] =>
  first [ constr_eq m nm | try clear nm; rename m into nm ] end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ------------------------------------------------------------------ the seat at 0x82b3c *)
(* registers: atoms (s0 = fd, s2 = SB atom 18); atom 32 = |es|, 33 = the capacity, 34 = T (the extra atoms);
   the three globals read-only at their object atoms; image-band facts on the object atoms and on the auipc images
   of g_capsrc / g_src (the store regions after realloc are based there). *)
Definition HD_PHI : Z := 140737479966720.
Definition HD_IMG : afact := mkAF 65536 6275064 0.
Definition HD_HI : afact := mkAF 32768 6275072 0.
Definition hd_Bx : sv := SOff 18 0.
Definition hd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition hd_nsrc_r : YP09.region := YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition hd_capsrc_r : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition hd_src_r : YP09.region := YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition hd_facts : facts :=
mkFacts [ (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 3 0); (33%nat, mkAF 0 16 0); (34%nat, mkAF 0 HD_PHI 0);
  (A_OBJ 4, HD_IMG); (A_OBJ 13, HD_IMG); (A_OBJ 5, HD_IMG); (A_HI 29, HD_HI); (A_HI 30, HD_HI) ] [] [].
Definition ss_hd : sstate := mkSS A_ra_held sr_atoms [hd_nsrc_r; hd_capsrc_r; hd_src_r] None hd_facts.
Definition hd_extra (n c t : Z) : list word := map (Z_to_bv 64) [n; c; t].
(* the store windows after realloc: g_src at s4 + 500 (s4 = atom A_HI 30 = 310), g_capsrc at s5 + 576 (s5 = atom
   A_HI 29 = 309); the bases are written as the numerals a normalised state carries *)
Definition hd_src_w : YP09.region := YP09.mkRegion (Some 310%nat) 500 508 500 508 [].
Definition hd_cap_w : YP09.region := YP09.mkRegion (Some 309%nat) 576 580 576 580 [].
(* the registers HELD never writes (sp, gp, tp, s0 = fd, s2 = SB, s7 .. s11) *)
Definition HD_KEPT : list (bv 5) := [2; 3; 4; 8; 18; 23; 24; 25; 26; 27]%bv.

Lemma hd_mbyte_of_apresent : forall H (m : word -> option byte) a,
apresent H m a -> exists b, mbyte SEGS (mrestrict H m) a = Some b.
Proof. intros H m a (Hh & b & Hb). exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.

(* W_gse_loop.v's gsl_writable_view / gsl_view_some / gsl_vm_kept *)
Lemma hd_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
Lemma hd_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma hd_vm_kept : forall H H' (m m' : word -> option byte) a n v, val_mem SEGS (mrestrict H m) a n v ->
(forall b, a <= b < a + Z.of_nat n -> aview SEGS H' m' b = aview SEGS H m b) -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply (val_mem_kept SEGS H H' m m' a n v); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
(* the bytes a live block holds, as a byte list (atable_at's tail) *)
Lemma hd_tail : forall (m : word -> option byte) (n : nat) a,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte SEGS m (a + i) = Some b) ->
exists l : list byte, length l = n /\ garr8 SEGS m a (bzs l).
Proof.
induction n as [|n IH]; intros a Hb.
- exists []. split; [reflexivity|]. intros j Hj. cbn in Hj. lia.
- destruct (Hb 0 ltac:(lia)) as (b0 & Hb0). rewrite Z.add_0_r in Hb0.
  destruct (IH (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hb; lia)) as (l & Hl & Hg).
  exists (b0 :: l). split; [cbn; rewrite Hl; reflexivity|].
  intros [|j] Hj; cbn [bzs map nth].
  + split; [|unfold bz; pose proof (bv_unsigned_in_range 8 b0) as Hr; change (bv_modulus 8) with 256 in Hr; lia].
    intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite !Z.add_0_r, Hb0. f_equal.
    apply bv_eq. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia.
    rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b0) as Hr. change (bv_modulus 8) with 256 in Hr.
    change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
  + cbn [length bzs map] in Hj. destruct (Hg j ltac:(unfold bzs in *; rewrite length_map in *; lia)) as (Hv & Hr).
    unfold bzs in Hv, Hr. replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. split; assumption.
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round's record (W_journal_x.v Record roomp): the room invariant rp_RM with its laws rp_RMM / rp_RPF *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
(* the allocator rules' caller-context table (W_contract_x.v Section w5's CTX; W_journal_x.v Section hc, the _c rules) *)
Variable CTX : list (list Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (RA_G RG).
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_capsrc RG.
Hypothesis HH28 : VAL (A_HI 28) + RA_HI_NSRC = rg_nsrc RG.
Hypothesis HH29 : VAL (A_HI 29) + RA_HI_CAPSRC = rg_capsrc RG.
Hypothesis HH30 : VAL (A_HI 30) + RA_HI_SRC = rg_src RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
Hypothesis HMMAX : ATABLE < MMAX.
(* realloc at the caller-context rule in the room form (W_journal_x.v Section hc): its pre asks the room budget
   rp_RM RP Sc (2 + kr), the live counts cnt_ok and the stack room below the call; its post gives rp_RM RP S2 kr *)
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX (SIGMA WS_realloc).
(* forced by the generic placement PST (lib/B/W_op_add.v Section x's HPST text): the ROM-view lemma
   ajournal_gx_rom_view_x asks the ROM bytes off PST.  Trivial at PST = [] *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.

(* ROM is image, so off PST *)
Lemma hd_pstr : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.
(* a byte of RA_G lies in the image *)
Lemma hd_inG_img : forall a, inG (RA_G RG) a -> 0x10000 <= a < 0x5fc000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
(* W_gestures_end.v gse_not_owned, over ARx *)
Lemma hd_not_owned_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* a byte a reader sees, off the read-only segments, is writable *)
Lemma hd_wr_of_view : forall H (m : word -> option byte) a, 0 <= a < 2 ^ 64 ->
aview SEGS H m a <> None -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a Ha Hv Hn. destruct (aview SEGS H m a) as [v|] eqn:Ev;
[exact (hd_writable_view H m a v Ha Ev Hn) | exfalso; exact (Hv eq_refl)].
Qed.

Lemma hd_seat : forall cx regs1 (W1 : world SEGS) m1 n c t,
bregs_held cx regs1 ->
val_mem SEGS (arm W1 m1) (rg_nsrc RG) 4 n -> val_mem SEGS (arm W1 m1) (rg_capsrc RG) 4 c ->
val_mem SEGS (arm W1 m1) (rg_src RG) 8 t ->
0 <= n <= 3 -> 0 <= c <= 16 -> 0 <= t <= HD_PHI ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (hd_extra n c t))) ss_hd
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_ra_held)) m1 (seg_rom SEGS)))
/\ sh_ok SEGS hd_Bx [] (Eimg (Ereg regs1 (hd_extra n c t))) (mrestrict (w_H W1) m1).
Proof.
intros cx regs1 W1 m1 n c t HRH Vn Vc Vt Hn Hc Ht.
destruct HRH as (_ & _ & R18).
pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 13 ltac:(lia)) as O13.
pose proof (pa_obj_img 5 ltac:(lia)) as O5.
rewrite HV4 in O4. rewrite HV13 in O13. rewrite HV5 in O5.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (hd_extra n c t))).
assert (UV : forall a w, (A_TEXT <= a < A_LIM)%nat -> VAL a = w -> bv_unsigned (ew E a) = w).
{ intros a w Ha Hw. subst E. rewrite (Eimg_img _ a Ha). rewrite unsigned_lit_small; [exact Hw|].
  pose proof (pa_val_range a). lia. }
assert (U18 : bv_unsigned (ew E 18) = SB).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl), R18.
  apply unsigned_lit_small. cbv [SB SHADOW_OFF]. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = t) by (rewrite E34; apply unsigned_lit_small; unfold HD_PHI in *; lia).
assert (U4 : bv_unsigned (ew E (A_OBJ 4)) = rg_nsrc RG) by (apply UV; [unfold A_OBJ, A_TEXT, A_LIM; lia | exact HV4]).
assert (U13 : bv_unsigned (ew E (A_OBJ 13)) = rg_capsrc RG) by (apply UV; [unfold A_OBJ, A_TEXT, A_LIM; lia | exact HV13]).
assert (U5 : bv_unsigned (ew E (A_OBJ 5)) = rg_src RG) by (apply UV; [unfold A_OBJ, A_TEXT, A_LIM; lia | exact HV5]).
assert (UH29 : bv_unsigned (ew E (A_HI 29)) = rg_capsrc RG - 576)
  by (apply UV; [unfold A_HI, A_TEXT, A_LIM; lia | unfold RA_HI_CAPSRC in HH29; lia]).
assert (UH30 : bv_unsigned (ew E (A_HI 30)) = rg_src RG - 500)
  by (apply UV; [unfold A_HI, A_TEXT, A_LIM; lia | unfold RA_HI_SRC in HH30; lia]).
split.
- unfold ss_hd. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, hd_nsrc_r, hd_capsrc_r, hd_src_r;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U4. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (YI04.chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Vn.
    * rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (YI04.chunk_ok_val SEGS E _ (rg_capsrc RG) 0 4 (SOff 33 0) c);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Vc.
    * rewrite U5. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (YI04.chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 34 0) t);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold HD_PHI in *; zside | zside |].
      rewrite Z.add_0_r. exact Vt.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi hd_nsrc_r hd_capsrc_r hd_src_r base_val].
    rewrite U4, U13, U5. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    ra_pick HRGP 3%nat 4%nat D34. ra_pick HRGP 3%nat 5%nat D35. ra_pick HRGP 4%nat 5%nat D45.
    revert D34 D35 D45. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [hd_facts f_atoms atoms_ok]. unfold afact_ok, HD_IMG, HD_HI. cbn [af_lo af_hi af_al2].
    rewrite U18, U32, U33, U34, U4, U13, U5, UH29, UH30.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hn Hc Ht O4 O13 O5. clear. unfold SB, HD_PHI. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor.
Qed.

(* realloc (0, n) at its entry: AREALLOC (the room form) on the inner journal of the ajournal_gx_x, repacked
   (W_gestures_end.v gse_free's form).  The stack room below the call is the journal's (aj_stack_room_x). *)
Lemma hd_realloc_x : forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch (kr : nat),
ajournal_gx_x SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 -> getr regsT 11 = w64 n ->
1 <= n < MMAX -> blocks_bytes Sc + n <= LIVE_MAX ->
cnt_ok RP (ablocks B lyc Sc) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX ->
rp_RM RP Sc (2 + kr) ->
mo_ok MT Sc (mo_malloc MT n + mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_realloc)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 res,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_x SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\ 4096 <= res /\
Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B lyc Sc) /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n + mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) H10 H11 Hn HL HCNT Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch Hctx HRM MOK.
rewrite !Z.add_0_r in HJi.
eapply SRr_mono.
{ exact (AREALLOC W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k 0 0 n o raw ch kr HJi (or_introl eq_refl)
    H10 H11 Hn HL HCNT Hsp Hal Hneg Hst
    (aj_stack_room_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k o regsT HJi Hsp Hst)
    Hgp Htp Hra Hraw Hch Hctx HRM (fun Hp0 => False_ind _ (Hp0 eq_refl)) MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10' & HFR & Hres & HPm & _ & _ & HK
  & HM & HRM2 & HE & HPr).
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [reflexivity|].
split; [apply (ajournal_gx_pack_x SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3)
  memS); [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exact H10'|]. split; [exact HFR|]. split; [exact Hres|].
split; [exact (HPm eq_refl)|].
split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a [Ha | [Hne _]]; [exact Ha | exfalso; exact (Hne eq_refl)]]|].
split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
intros a Hi Ho He Hpa.
apply HPr; [exact Hi | exact (hd_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (hd_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hpa].
intros [Hr | [Hne _]]; [|exact (Hne eq_refl)].
assert (Hin : In (res, n) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact (HPm eq_refl) | left; reflexivity]).
exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res n a (proj1 HJ2) Hin Hr Hi).
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this segment at a world relation R, over the cut interface's R forms
   (W_relay_add_cut_x.v Section cR): its runs and branches at their G twins, and its one call, the realloc, by
   its R rule AREALLOC_R.  At the cf instance R := wle' SEGS RZ_cf. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HAD : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
(* the realloc's hull admission at the call, from the meter's mo_ok at the call: at reply's top
   HAD := (fun _ Sc _ _ _ n => cf_hull_adm Sc n), and the top discharges HA_ra from the meter *)
Hypothesis HA_ra : forall lyc Sc regsT ch p n, 1 <= n -> mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HAD lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HAD CTX R (SIGMA WS_realloc).
Let RUNR := paj_run_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Lemma hd_realloc_xR : forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch (kr : nat),
ajournal_gx_xR SEGS B PST ARx R (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 0 -> getr regsT 11 = w64 n ->
1 <= n < MMAX -> blocks_bytes Sc + n <= LIVE_MAX ->
cnt_ok RP (ablocks B lyc Sc) ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX ->
rp_RM RP Sc (2 + kr) ->
mo_ok MT Sc (mo_malloc MT n + mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA WS_realloc)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 res,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_xR SEGS B PST ARx R (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\ 4096 <= res /\
Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B lyc Sc) /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n) /\
mo_le MT Sc S2 (mo_malloc MT n + mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) H10 H11 Hn HL HCNT Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch Hctx HRM MOK.
rewrite !Z.add_0_r in HJi.
eapply SRrG_mono.
{ exact (AREALLOC_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k 0 0 n o raw ch kr HJi (or_introl eq_refl)
    H10 H11 Hn HL HCNT Hsp Hal Hneg Hst
    (aj_stack_room_xR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k o regsT HJi Hsp Hst)
    Hgp Htp Hra Hraw Hch (RO_ARx _ _ _ _ _ _ (proj1 HJi))
    (HA_ra _ _ _ _ _ _ (proj1 Hn) MOK) Hctx HRM (fun Hp0 => False_ind _ (Hp0 eq_refl)) MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10' & HFR & Hres & HPm & _ & _ & HK
  & HM & HRM2 & HE & HPr).
exists ly2, S2, Hp2, regs2, mem2, md2, res. split; [reflexivity|].
split; [apply (ajournal_gx_pack_xR SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 3)
  memS); [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
split; [exact HP2|]. split; [exact H10'|]. split; [exact HFR|]. split; [exact Hres|].
split; [exact (HPm eq_refl)|].
split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a [Ha | [Hne _]]; [exact Ha | exfalso; exact (Hne eq_refl)]]|].
split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
intros a Hi Ho He Hpa.
apply HPr; [exact Hi | exact (hd_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (hd_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hpa].
intros [Hr | [Hne _]]; [|exact (Hne eq_refl)].
assert (Hin : In (res, n) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact (HPm eq_refl) | left; reflexivity]).
exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res n a (proj1 HJ2) Hin Hr Hi).
Qed.
Theorem pb_rb_held_xR : rb_held_stmtR B PST ARx MT RP G RG CTX R.
Proof.
intros cx W1 c1 HB (regs1 & m1 & md1 & -> & HRH & Hfd0 & HAL & HREL) KRAA.
pose proof HAL as (HJ & HROM1 & HPK1 & HSV & HLK & HWAKE & HFR & HERR1).
pose proof HB as (HPRE & Hal32 & Hcnt & H10 & Hfdr & _ & _ & HROM0 & _ & HNEW & HGin & HGerr & HROOM & HCTX & HMOK
  & HRM & HPK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof HRH as ((Rsp & Rgp & Rtp & R23 & R24 & R25 & R26 & R27) & R8 & R18).
destruct (HNEW Hfd0) as (Hlen4 & _).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
(* the cells of RA_G and g_wake[1], in the image *)
assert (IL : forall a, rg_lock RG <= a < rg_lock RG + 12 -> inG (RA_G RG) a) by (intros a Ha; apply ra_lock_in; exact Ha).
assert (IN : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> inG (RA_G RG) a) by (intros a Ha; apply ra_nsrc_in; exact Ha).
assert (IC : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> inG (RA_G RG) a) by (intros a Ha; apply ra_capsrc_in; exact Ha).
assert (IS : forall a, rg_src RG <= a < rg_src RG + 8 -> inG (RA_G RG) a) by (intros a Ha; apply ra_src_in; exact Ha).
assert (BL : 0x10000 <= rg_lock RG /\ rg_lock RG + 12 <= 0x5fc000)
  by (pose proof (hd_inG_img _ (IL (rg_lock RG) ltac:(lia))); pose proof (hd_inG_img _ (IL (rg_lock RG + 11) ltac:(lia))); lia).
assert (BN : 0x10000 <= rg_nsrc RG /\ rg_nsrc RG + 4 <= 0x5fc000)
  by (pose proof (hd_inG_img _ (IN (rg_nsrc RG) ltac:(lia))); pose proof (hd_inG_img _ (IN (rg_nsrc RG + 3) ltac:(lia))); lia).
assert (BC : 0x10000 <= rg_capsrc RG /\ rg_capsrc RG + 4 <= 0x5fc000)
  by (pose proof (hd_inG_img _ (IC (rg_capsrc RG) ltac:(lia))); pose proof (hd_inG_img _ (IC (rg_capsrc RG + 3) ltac:(lia))); lia).
assert (BS : 0x10000 <= rg_src RG /\ rg_src RG + 8 <= 0x5fc000)
  by (pose proof (hd_inG_img _ (IS (rg_src RG) ltac:(lia))); pose proof (hd_inG_img _ (IS (rg_src RG + 7) ltac:(lia))); lia).
assert (BW : 0x10000 <= rg_wake RG + 4 /\ rg_wake RG + 8 <= 0x5fc000)
  by (pose proof (pa_img_range _ (proj1 (HWK (rg_wake RG + 4) ltac:(lia))));
      pose proof (pa_img_range _ (proj1 (HWK (rg_wake RG + 7) ltac:(lia)))); lia).
(* the three cells at the entry, in one form for both arms of ra_rel *)
assert (VALS : val_mem SEGS (arm W1 m1) (rg_nsrc RG) 4 (Z.of_nat (length (bxes cx))) /\
  val_mem SEGS (arm W1 m1) (rg_capsrc RG) 4 (if bxT cx =? 0 then 0 else 16) /\
  val_mem SEGS (arm W1 m1) (rg_src RG) 8 (bxT cx) /\ 0 <= bxT cx <= HD_PHI).
{ destruct HREL as [(HT0 & Hes0 & HE0) | HRA].
  - rewrite HT0, Hes0. cbn [length Z.of_nat Z.eqb]. destruct HE0 as (V8 & _ & V4 & _ & V4c & _).
    split; [exact V4 | split; [exact V4c | split; [exact V8 | unfold HD_PHI; lia]]].
  - destruct HRA as (V8 & _ & V4 & _ & V4c & _ & _ & Hin & _).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 Hin) as (_ & H4096 & Hc & _).
    rewrite (proj2 (Z.eqb_neq (bxT cx) 0) ltac:(lia)).
    split; [exact V4 | split; [exact V4c | split; [exact V8|]]].
    change (req_size ATABLE) with 896 in Hc. unfold HD_PHI. lia. }
destruct VALS as (Vn & Vc & Vt & Ht).
remember (Z.of_nat (length (bxes cx))) as NE eqn:HNE.
remember (if bxT cx =? 0 then 0 else 16) as CP eqn:HCP.
assert (HNEb : 0 <= NE <= 3) by (rewrite HNE; lia).
assert (HCPb : 0 <= CP <= 16) by (rewrite HCP; destruct (bxT cx =? 0); lia).
destruct (hd_seat cx regs1 W1 m1 NE CP (bxT cx) HRH Vn Vc Vt HNEb HCPb Ht) as [HS SHOK].
remember (Eimg (Ereg regs1 (hd_extra NE CP (bxT cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (hd_extra NE CP (bxT cx))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 NE) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 CP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (bxT cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE.
(* the auipc images s3 (atom 308 = A_HI 28) and s4 (atom 310 = A_HI 30), in any image environment *)
assert (U308 : forall Ex, img_env VAL A_LIM Ex -> ew Ex 308 = w64 (rg_nsrc RG - RA_HI_NSRC)).
{ intros Ex HEx. rewrite (img_env_atomP Ex 308 HEx ltac:(cbv; lia)). unfold w64. f_equal.
  change (VAL 308%nat) with (VAL (A_HI 28)). lia. }
assert (U310 : forall Ex, img_env VAL A_LIM Ex -> ew Ex 310 = w64 (rg_src RG - RA_HI_SRC)).
{ intros Ex HEx. rewrite (img_env_atomP Ex 310 HEx ltac:(cbv; lia)). unfold w64. f_equal.
  change (VAL 310%nat) with (VAL (A_HI 30)). lia. }
unfold cfg_at. change (w64 (BASE + A_ra_held)) with (Z_to_bv 64 (BASE + A_ra_held)).
(* 0x82b3c -> 0x82b50: the auipc images, the loads of g_nsrc / g_capsrc, to the `bne` *)
paj_run_tok_xR RUNR HS HJ SHOK hd_Bspan.
{ hd_nowr. }
hd_mem Em1.
psrr_branch_tok RUNR BRR HS SHOK hd_Bspan.
- (* bne TAKEN: |es| <> the capacity, so the table exists (T <> 0); to 0x82b90, RBAR with T1 = T *)
  rewrite branch_ne_U, (U_atom E 32 NE E32 ltac:(lia)), (U_atom E 33 CP E33 ltac:(lia)) in Hc.
  apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  assert (HT : bxT cx <> 0).
  { intros HT0. rewrite HT0 in HCP. cbn in HCP.
    destruct HREL as [(_ & Hes0 & _) | HRA0]; [rewrite Hes0 in HNE; cbn in HNE; lia|].
    destruct HRA0 as (_ & _ & _ & _ & _ & _ & _ & Hin & _). rewrite HT0 in Hin.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 Hin) as (_ & H4096 & _). lia. }
  assert (HRA : arelay_at B RG (bxly cx) (bxS cx) W1 m1 (bxT cx) (bxes cx))
    by (destruct HREL as [(HT0 & _) | HRA]; [exfalso; exact (HT HT0) | exact HRA]).
  (* no allocator call on this arm: the room is the entry's budget, ra_cost MT_rk T = 0 *)
  assert (HRMk : rp_RM RP (bxS cx) (bxkr cx))
    by (unfold ra_cost in HRM; rewrite (proj2 (Z.eqb_neq _ 0) HT) in HRM; exact HRM).
  paj_run_to_tok_xR RUNTOR HS HJ SHOK hd_Bspan A_ra_app.
  { hd_nowr. }
  hd_mem Em2.
  hd_cur HS msx.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ HD_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  pmkst HS. rewrite Em2, Em1 in HJ |- *.
  apply KRAA. exists (ms_regs msx), (bxly cx), (bxS cx), (bxHp cx), m1. eexists. exists 0, (bxT cx).
  split; [reflexivity|].
  split; [unfold bregs_held, bregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
  split; [rewrite N19; exact (U308 E HEI)|].
  split; [rewrite N20; exact (U310 E HEI)|].
  split; [exact Hfd0|].
  split; [split; [exact HJ | exact (conj HROM1 (conj HPK1 (conj HSV (conj HLK (conj HWAKE (conj HFR HERR1))))))]|].
  split; [exact HRA|].
  split; [unfold ra_cost; rewrite (proj2 (Z.eqb_neq _ 0) HT); apply (mo_le_refl MT MTL)|].
  split; [exact HRMk|].
  right. split; [exact HT|]. split; reflexivity.
- (* bne NOT TAKEN: |es| = the capacity, so T = 0 and es = [] *)
  rewrite branch_ne_U, (U_atom E 32 NE E32 ltac:(lia)), (U_atom E 33 CP E33 ltac:(lia)) in Hc.
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  assert (HT0 : bxT cx = 0).
  { destruct (Z.eq_dec (bxT cx) 0) as [h|h]; [exact h|]. exfalso.
    rewrite (proj2 (Z.eqb_neq _ 0) h) in HCP. lia. }
  assert (Hes0 : bxes cx = []).
  { destruct HREL as [(_ & Hes & _) | HRA0]; [exact Hes|]. exfalso.
    destruct HRA0 as (_ & _ & _ & _ & _ & _ & _ & Hin & _). rewrite HT0 in Hin.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR1 Hin) as (_ & H4096 & _). lia. }
  assert (HNE0 : NE = 0) by (rewrite HNE, Hes0; reflexivity).
  (* 0x82b50 -> `beqz a0` 0x82b54 (a0 = |es|, atom 32).  Its not-taken arm holds the int32 doubling guard and the
     TRAP 0x82b60; it is refuted here from a0 = |es| = 0. *)
  paj_run_tok_xR RUNR HS HJ SHOK hd_Bspan.
  { hd_nowr. }
  hd_mem Em2.
  psrr_branch_tok RUNR BRR HS SHOK hd_Bspan.
  2: { exfalso. lazymatch goal with Hc0 : branch_taken _ _ _ = false |- _ =>
       rewrite ?branch_eq_U, ?branch_ne_U in Hc0;
       rewrite ?(U_atom E 32 NE E32 ltac:(lia)), ?(U_lit E 0 ltac:(lia)) in Hc0;
       rewrite HNE0 in Hc0; cbn in Hc0; discriminate Hc0 end. }
  (* 0x82b6c -> the realloc PCall 0x82b80: s6 = 16, a0 = g_src (atom 34 = T = 0), a1 = 56 * 16 = 896 *)
  paj_run_tok_xR RUNR HS HJ SHOK hd_Bspan.
  { hd_nowr. }
  hd_mem Em3.
  hd_cur HS msc.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  assert (QSP : spZ (ms_regs msc) = bsp0 cx + -64).
  { unfold spZ. rewrite Q2, (EEo 2%nat 2%bv eq_refl). change (bv_unsigned (getr regs1 2)) with (spZ regs1).
    rewrite Rsp. unfold RA_FRAME. lia. }
  assert (QS0 : s0Z (ms_regs msc) = bxfd cx).
  { unfold s0Z. rewrite Q8, (EEo 8%nat 8%bv eq_refl), R8. unfold w64. apply unsigned_lit_small. lia. }
  assert (QRA : raZ (ms_regs msc) = BASE + 2112).
  { unfold raZ. rewrite Q1. apply unsigned_lit_small. lia. }
  assert (Q10' : getr (ms_regs msc) 10 = w64 0) by (rewrite Q10, E34, HT0; reflexivity).
  assert (Q11' : getr (ms_regs msc) 11 = w64 ATABLE) by (rewrite Q11; reflexivity).
  (* the room at the call: ra_spec_x's budget at T = 0 (ra_cost MT_rk 0 = 2, the realloc's own charge), and the live
     counts at the call's state (the entry's: the lock left the allocator state as it was), from ra_peak 0 *)
  assert (HRM2k : rp_RM RP (bxS cx) (2 + bxkr cx)).
  { rewrite HT0 in HRM. change (Z.to_nat (ra_cost MT_rk 0)) with 2%nat in HRM. exact HRM. }
  assert (HCNT : cnt_ok RP (ablocks B (bxly cx) (bxS cx))).
  { unfold cnt_ok.
    apply (cnt_ok_pk_mono RP (ra_peak (bxT cx)) (fun _ => 0%nat) (ablocks B (bxly cx) (bxS cx))
      (ablocks B (bxly cx) (bxS cx))); [intros P; cbv beta; lia | exact HPK]. }
  pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (hd_realloc_xR W1 (ms_regs msc) m1 RA_STK (bsp0 cx) (bFP cx) (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx)
      (bxmd cx) [] (bxly cx) (bxS cx) (bxHp cx) _ 0 ATABLE (-64) (getr (ms_regs msc) 1) [] (bxkr cx) HJ).
    - exact Q10'.
    - exact Q11'.
    - unfold ATABLE in *. lia.
    - exact (HROOM Hfd0 HT0).
    - exact HCNT.
    - exact QSP.
    - reflexivity.
    - lia.
    - unfold RA_STK, RA_FRAME, ASTACK. lia.
    - rewrite Q3, (EEo 3%nat 3%bv eq_refl), Rgp. exact Hgp.
    - rewrite Q4, (EEo 4%nat 4%bv eq_refl), Rtp. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - apply (achain_chain_pre (bxly cx) _ (spZ (ms_regs msc)) (s0Z (ms_regs msc)) [] (ms_regs msc)).
      + apply achain_low. rewrite QS0. lia.
      + rewrite QSP. unfold bsp0, RA_STK, RA_FRAME, ASTACK in *. lia.
      + reflexivity.
      + rewrite QRA. lia.
    - (* the caller context (ra_spec_x's In [pc + 144] CTX): ch = [], ra = entry + 144 = BASE + 2112 *)
      rewrite QRA. cbn [spine map].
      replace (BASE + 2112) with (A_relay_addP + 144) by (unfold A_relay_addP, A_relay_add, AF_fr_relay_add; lia).
      exact HCTX.
    - exact HRM2k.
    - unfold ra_cost in HMOK. rewrite HT0, Z.eqb_refl in HMOK. exact HMOK. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10r & HFR2 & Hres & HPm & HK2
    & HM2 & HRM2 & HE2 & HPK2).
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (Hin2 : In (res, ATABLE) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HPm | left; reflexivity]).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (Hr16 & Hr4096 & Hrc & _ & _ & _).
  change (req_size ATABLE) with 896 in Hrc.
  (* back at 0x82b84: no region is kept across the call (the code after it reads no memory) *)
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { constructor. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (HAEb : env_agree 32 (Ereg regs1 (hd_extra NE CP (bxT cx))) Eb)
    by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  assert (E44 : ew Eb 44 = w64 res).
  { rewrite HEb. refine (eq_trans (ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia)) _).
    cbv [CLOB map nth]. exact H10r. }
  clear HEb.
  assert (UH29 : bv_unsigned (ew Eb 309) = rg_capsrc RG - 576).
  { rewrite (HEIb 309%nat ltac:(cbv; lia)). change (VAL 309%nat) with (VAL (A_HI 29)). unfold RA_HI_CAPSRC in HH29. lia. }
  assert (UH30 : bv_unsigned (ew Eb 310) = rg_src RG - 500).
  { rewrite (HEIb 310%nat ltac:(cbv; lia)). change (VAL 310%nat) with (VAL (A_HI 30)). unfold RA_HI_SRC in HH30. lia. }
  (* the realloc's block (atom 44): >= 4096, 16-aligned: the runner refutes `beqz a0` 0x82b84 (the error path) *)
  pose proof (st_ok_pi_add_fact Eb _ _ 44 (mkAF 4096 HD_PHI 4) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E44; unfold w64;
          rewrite unsigned_lit_small by (unfold HD_PHI; lia); change (2 ^ 4) with 16; unfold HD_PHI;
          repeat split; lia)) as HSa.
  clear HS; rename HSa into HS. norm_ss HS.
  (* the cells realloc does not touch: the image bytes of RA_G and g_wake[1] *)
  assert (KG2 : forall a, inG (RA_G RG) a \/ (rg_wake RG + 4 <= a < rg_wake RG + 8) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) m1 a).
  { intros a [Ha | Ha].
    - destruct (HG a Ha) as (Hi & Ho & _). exact (proj1 (proj2 (proj2 HK2)) a Hi Ho (HGerr a Ha)).
    - destruct (HWK a Ha) as (Hi & Ho & He). exact (proj1 (proj2 (proj2 HK2)) a Hi Ho He). }
  assert (WRs : forall i, 0 <= i < 8 -> writable_at SEGS (mrestrict (w_H W2) mem2) (rg_src RG + i)).
  { intros i Hi. apply hd_wr_of_view; [lia | | apply HNROM, IS; lia].
    rewrite KG2 by (left; apply IS; lia). exact (hd_view_some (w_H W1) m1 (rg_src RG) 8 (bxT cx) i Vt Hi). }
  assert (WRc : forall i, 0 <= i < 4 -> writable_at SEGS (mrestrict (w_H W2) mem2) (rg_capsrc RG + i)).
  { intros i Hi. apply hd_wr_of_view; [lia | | apply HNROM, IC; lia].
    rewrite KG2 by (left; apply IC; lia). exact (hd_view_some (w_H W1) m1 (rg_capsrc RG) 4 CP i Vc Hi). }
  (* the two store windows, at the kept auipc registers s4 (+ 500) and s5 (+ 576) *)
  pose proof (st_ok_pi_add_region Eb _ _ hd_src_w HS ltac:(vm_compute; reflexivity)
    ltac:(unfold region_ok, hd_src_w;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite UH30; split; [lia|]; split; [lia|]; split;
      [ intros o Ho; replace (rg_src RG - 500 + o) with (rg_src RG + (o - 500)) by lia; apply WRs; lia
      | apply Forall_nil ])
    ltac:(cbn; exact I)) as HSa.
  clear HS; rename HSa into HS. norm_ss HS.
  pose proof (st_ok_pi_add_region Eb _ _ hd_cap_w HS ltac:(vm_compute; reflexivity)
    ltac:(unfold region_ok, hd_cap_w;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite UH29; split; [lia|]; split; [lia|]; split;
      [ intros o Ho; replace (rg_capsrc RG - 576 + o) with (rg_capsrc RG + (o - 576)) by lia; apply WRc; lia
      | apply Forall_nil ])
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint, hd_cap_w; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite UH29, UH30; split; [|exact I]; ra_pick HRGP 4%nat 5%nat D45; lia)) as HSa.
  clear HS; rename HSa into HS. norm_ss HS.
  assert (SHOK2 : sh_ok SEGS hd_Bx [] Eb (mrestrict (w_H W2) mem2)) by constructor.
  rewrite Q1.
  (* 0x82b84 -> 0x82b90: `beqz a0` not taken, g_src = a0, g_capsrc = 16 *)
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 hd_Bspan A_ra_app.
  { apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UH29 in Ha; apply IC; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UH30 in Ha; apply IS; lia |].
    apply awr_ok_x_nil. }
  hd_cur HS msf.
  match goal with Hx : ajournal_gx_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msf) _ _ |- _ => rename Hx into HJ3 end.
  match goal with Hx : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem msf)) |- _ => rename Hx into HFr3 end.
  match goal with Hx : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem msf)) |- _ => rename Hx into HG3 end.
  pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin2) as (_ & _ & _ & _ & Hrp3 & _).
  change (req_size ATABLE) with 896 in Hrp3.
  (* the run wrote only the two store windows *)
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_src RG <= a < rg_src RG + 8) -> ~ (rg_capsrc RG <= a < rg_capsrc RG + 4) ->
    aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha N1 N2. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msf) HFr3 a Ha).
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?UH29, ?UH30 in Hr; lia | ]).
    destruct Hin. }
  assert (KALL : forall a, (inG (RA_G RG) a \/ (rg_wake RG + 4 <= a < rg_wake RG + 8)) ->
    ~ (rg_src RG <= a < rg_src RG + 8) -> ~ (rg_capsrc RG <= a < rg_capsrc RG + 4) ->
    aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha N1 N2. rewrite <- (KG2 a Ha). apply KR3; [|exact N1 | exact N2].
    destruct Ha as [Ha | Ha]; [pose proof (hd_inG_img a Ha) |]; lia. }
  (* the frame (the saved registers): above the realloc's scratch, and not a store window *)
  assert (KHI : forall a, bsp0 cx - 64 <= a < bsp0 cx -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W1) m1 a).
  { intros a Ha. unfold bsp0 in *.
    rewrite (KR3 a ltac:(unfold RA_STK, RA_FRAME, ASTACK in *; lia) ltac:(unfold RA_STK, RA_FRAME, ASTACK in *; lia)
      ltac:(unfold RA_STK, RA_FRAME, ASTACK in *; lia)).
    apply (proj1 HK2); unfold RA_STK, RA_FRAME, ASTACK in *; lia. }
  pmkst HS.
  prreg HS (19%bv : bv 5) N19. prreg HS (20%bv : bv 5) N20.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ HD_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as RC.
  pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as RS.
  cbn [ms_mem restrict] in RC, RS.
  apply KRAA. exists (ms_regs msf), ly2, S2, Hp2, (ms_mem msf). eexists. exists (0 + 3), res.
  split; [reflexivity|].
  split; [unfold bregs_held, bregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
  split; [rewrite N19; exact (U308 Eb HEIb)|].
  split; [rewrite N20; exact (U310 Eb HEIb)|].
  split; [exact Hfd0|].
  split.
  { split; [exact HJ3|].
    split.
    { eapply ajournal_gx_rom_view_xR.
      all: first [exact HJ3 | exact HROMO | exact hd_pstr | exact HROM0 | exact LAWS | exact pa_segs_low]. }
    split.
    { intros a Hi Ho He Hpa. apply (apresent_grows (w_H W2) mem2 (ms_mem msf) a HG3).
      apply (HPK2 a Hi Ho He). exact (HPK1 a Hi Ho He Hpa). }
    split.
    { intros i Hi. apply (hd_vm_kept _ _ _ _ _ 8%nat _ (HSV i Hi)).
      intros b Hb. apply KHI. unfold RA_FRAME in Hb. lia. }
    split.
    { pose proof HLK as (LK0 & LK4 & LK8 & _).
      assert (KL : forall b, rg_lock RG <= b < rg_lock RG + 12 ->
        aview SEGS (w_H W2) (ms_mem msf) b = aview SEGS (w_H W1) m1 b).
      { intros b Hb. ra_pick HRGP 2%nat 4%nat D24. ra_pick HRGP 2%nat 5%nat D25.
        apply KALL; [left; apply IL; lia | lia | lia]. }
      split; [apply (hd_vm_kept _ _ _ _ _ 4%nat _ LK0); intros b Hb; apply KL; cbn in Hb; lia|].
      split; [apply (hd_vm_kept _ _ _ _ _ 4%nat _ LK4); intros b Hb; apply KL; cbn in Hb; lia|].
      split; [apply (hd_vm_kept _ _ _ _ _ 4%nat _ LK8); intros b Hb; apply KL; cbn in Hb; lia|].
      intros i Hi. apply hd_wr_of_view; [lia | | apply HNROM, IL; lia].
      rewrite KL by lia.
      destruct (Z_lt_ge_dec i 4) as [h1|h1]; [exact (hd_view_some _ _ _ 4%nat _ i LK0 ltac:(cbn; lia))|].
      destruct (Z_lt_ge_dec i 8) as [h2|h2].
      - replace (rg_lock RG + i) with (rg_lock RG + 4 + (i - 4)) by lia.
        exact (hd_view_some _ _ _ 4%nat _ (i - 4) LK4 ltac:(cbn; lia)).
      - replace (rg_lock RG + i) with (rg_lock RG + 8 + (i - 8)) by lia.
        exact (hd_view_some _ _ _ 4%nat _ (i - 8) LK8 ltac:(cbn; lia)). }
    split.
    { apply (hd_vm_kept _ _ _ _ _ 4%nat _ HWAKE). intros b Hb. cbn in Hb.
      ra_pick HRGP 4%nat 6%nat D46. ra_pick HRGP 5%nat 6%nat D56.
      apply KALL; [right; lia | lia | lia]. }
    split; [exact HFR2|].
    (* errno: kept by the realloc (its errno conjunct) and by the run (errno is no byte of RA_G, so in no store
       window) *)
    intros i Hi.
    assert (Hel : 0 <= as_errno B + i < kLowMemEnd)
      by first [ exact (proj1 (ra_errno_low B TL i Hi)) | exact (proj1 (ra_errno_low TL i Hi))
               | exact (proj1 (ra_errno_low B MT G RG TL i Hi)) ].
    rewrite (KR3 (as_errno B + i) ltac:(unfold kLowMemEnd in Hel; lia)
      ltac:(intros Hs; exact (HGerr _ (IS _ Hs) ltac:(lia)))
      ltac:(intros Hs; exact (HGerr _ (IC _ Hs) ltac:(lia)))).
    rewrite (HE2 i Hi). exact (HERR1 i Hi). }
  split.
  { rewrite Hes0. unfold arelay_at. cbn [length Z.of_nat].
    assert (KN : forall b, rg_nsrc RG <= b < rg_nsrc RG + 4 ->
      aview SEGS (w_H W2) (ms_mem msf) b = aview SEGS (w_H W1) m1 b).
    { intros b Hb. ra_pick HRGP 3%nat 4%nat D34. ra_pick HRGP 3%nat 5%nat D35.
      apply KALL; [left; apply IN; lia | lia | lia]. }
    rewrite HNE0 in Vn.
    split.
    { pose proof (field_of_region _ _ 310%nat _ _ _ _ _ _ 500 8%N (SOff 44 0) res RS UH30 ltac:(cbn; auto)
        ltac:(cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(cbn; unfold HD_PHI in *; lia) ltac:(cbn; lia)) as X.
      replace (rg_src RG - 500 + 500) with (rg_src RG) in X by lia. exact X. }
    split.
    { intros i Hi. destruct RS as (_ & _ & RW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RW.
      rewrite UH30 in RW. pose proof (RW (500 + i) ltac:(lia)) as X.
      replace (rg_src RG - 500 + (500 + i)) with (rg_src RG + i) in X by lia. exact X. }
    split.
    { apply (hd_vm_kept _ _ _ _ _ 4%nat _ Vn). intros b Hb. apply KN. cbn in Hb. lia. }
    split.
    { intros i Hi. apply hd_wr_of_view; [lia | | apply HNROM, IN; lia].
      rewrite KN by lia. exact (hd_view_some _ _ _ 4%nat _ i Vn Hi). }
    split.
    { pose proof (field_of_region _ _ 309%nat _ _ _ _ _ _ 576 4%N (SLit 16) 16 RC UH29 ltac:(cbn; auto)
        ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as X.
      replace (rg_capsrc RG - 576 + 576) with (rg_capsrc RG) in X by lia. exact X. }
    split.
    { intros i Hi. destruct RC as (_ & _ & RW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RW.
      rewrite UH29 in RW. pose proof (RW (576 + i) ltac:(lia)) as X.
      replace (rg_capsrc RG - 576 + (576 + i)) with (rg_capsrc RG + i) in X by lia. exact X. }
    split; [lia|].
    split; [exact Hin2|].
    split.
    { destruct (hd_tail (arm W2 (ms_mem msf)) 896 res) as (tl & Htl & Hg).
      { intros i Hi. unfold arm. apply hd_mbyte_of_apresent. exact (proj1 (Hrp3 (res + i) ltac:(lia))). }
      exists tl. unfold atable_at. cbn [map concat app length]. rewrite Htl.
      split; [reflexivity|]. split; [reflexivity | exact Hg]. }
    (* entries Forall, NoDup and arelay_at's 12th conjunct (no entry's block is the table block): es = [] *)
    split; [constructor|]. split; constructor. }
  split; [unfold ra_cost; rewrite HT0, Z.eqb_refl; exact HM2|].
  (* the room: the realloc rule's post *)
  split; [exact HRM2|].
  left. split; [exact HT0 | exact HPm].
Qed.
End cR.
(* the strict walk is its R twin at R := wle (route R's rule: one walk text; part 3c removed the temporary
   memnorm premise) *)
Theorem pb_rb_held_x : rb_held_stmt B PST ARx MT RP G RG CTX.
Proof.
eapply pb_rb_held_xR with (R := @wle _) (RO := fun _ => True) (HAD := fun _ _ _ _ _ _ => True);
  first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] | intros; exact I  | apply arealloc_cf_rule_c_xR_of_x; exact AREALLOC ].
Qed.
End c.
End b.
End a.
