(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the APP segment of the image-B walk of fuzz_reply's relay_add over a
   generic allocator relation ARx in the room form (lib/B/W_relay_add_cut_x.v rb_app_stmt): from the cut RBA (0x82b90,
   the table at T1 with the entry's es, the lock held) to the cut RBU (0x82c04, the entry ra_new fd appended).
   Donor: lib/B/W_relay_add_app.v pb_ra_app (the AR walk of the same stretch; its machine-code account below holds
   unchanged), converted by route (b) (CONVERSION.md sha256 1015972e02a9; internal record): the journal ajournal_gx ->
   W_journal_x.ajournal_gx_x (the ghost head set Hp after S), the runs paj_run_x / paj_run_to_x -> W_journal_x's
   paj_run_x_x / paj_run_to_x_x (through W_kit_x's paj_run_tok_x / paj_run_to_tok_x), the memset's lifting
   aj_gx_entry_at -> W_sites_x.aj_gx_entry_at_x and its contract AMEMSET -> W_sites_x.aintrin_realizes_x, AR's laws
   al_* -> AR_laws_x's alx_*, the table block's shadow and addressability range_addressable_of_block /
   shadow_hull_vis_of_block -> W_journal_x's _hp0_x forms under HP0 (a Theorem Labs lane's ruling), blk_off_imgP ->
   W_kit_xb.blk_off_imgB_x (image B's top 0x5fc000, at W_kit_x's IMGC / BLKN), W_relay_add_sep.v's AR lemmas -> their
   twins in lib/B/W_relay_add_sep_x.v.  rom_view at RBU is read off the kept bytes (every ROM byte is an image byte
   off g_nsrc, the heap slot and memset's scratch), not off the journal, so the walk needs no ROM-off-PST fact.
   The room: RBU's rp_RM RP S1 (bxkr cx) is RBA's (the stretch keeps the allocator state S1: memset is a runtime entry,
   the runs make no allocator call).  The AR-free parts of the donor (the byte and list lemmas, the seat ra_app_seat,
   the symbolic state, ra_efp_in_block / ra_eblks_in) are cited from lib/B/W_relay_add_app.v, not copied; its Ltac
   ra_mem, which does not leave the donor's Section b, is restated locally.

   The stretch (fuzz_reply.asan-ubsan), and how each of its five trap edges (all to `unimp` 0x82c80) is closed:
     0x82b90  s5 = g_nsrc (lw through A_HI 28), s4 = g_src (ld through A_HI 30), s1 = s4 + 56 s5
     0x82bb0  TRAP `snez a0,s4; seqz a1,s1; beq a0,a1` (null consistency): decided inside the run (snez = 1 from
              atom 33 = T1 >= 4096, seqz = 0 from atom 34 = the slot >= 4096).
     0x82bc4  TRAP `slti a0,s5,0; sltu a1,s1,s4; xor; xori 1; beqz` (pointer overflow): left open by the runner (the
              slot and T1 are distinct atoms); the taken arm is refuted by W_traps.v trap_ptr_sovf (slti folded to 0
              from atom 32's range [0, 3], sltu s1,s4 = 0 by trap_U_sltu_ge: T1 <= T1 + 56 |es|).
     0x82bd4  __asan_memset (s1, 0, 56) (AMEMSET, through W_sites_x.v aj_gx_entry_at_x; Wr = the slot's 56 bytes)
     0x82bdc  TRAP `addiw a0,s5,1; blt a0,s5` (int32 + 1 overflow): decided inside the run (a0 = atom 32 + 1 against
              atom 32, range [0, 3]).
     0x82be0  g_nsrc = |es| + 1 (sw through A_HI 28)
     0x82be4  TRAP `beqz s4` (null): decided inside the run (atom 33 >= 4096).
     0x82bec  TRAP `andi a0,s1,7; bnez` (alignment): decided inside the run (atom 34 8-aligned).
     0x82bf0  the shadow check of s1: decided by the shadow entry over the slot (the slow path 0x82c84 and the error
              path 0x82c90 are not reached)
     0x82c00  `sw s0,0(s1)`: the new entry's fd
   The seat holds g_nsrc and g_src read-only (both are only loaded before the call); after the call the region the
   store `sw a0,484(s3)` needs is seated at the auipc atom A_HI 28 (offset 484), and the new slot's first 4 bytes
   (the fd store) at the slot atom.  The old entries keep their bytes across the memset by W_relay_add_sep_x.v
   ra_efp_off_slot_x (no old entry reads the new slot).  errno's view (BLIVE's berrno_kept) is carried from RBA: errno is
   an image byte outside RA_G, so neither run nor the memset writes it. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_cut W_relay_add_sep W_relay_add_app.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_contract_x W_sites_x W_kit_x W_kit_xb W_relay_add_cut_x W_relay_add_sep_x.
(* route R: SRrG / wle' (YA0nH) and relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag the donor's proofs (converted here) run with, whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.
(* a run over read-only regions leaves the memory as it was (W_relay_add_app.v's ra_mem, whose Ltac does not leave
   that file's Section b) *)
Local Ltac ra_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round's record (W_journal_x.v Record roomp); the stretch only carries RBA's rp_RM to RBU *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable CTX : list (list Z).
Context {hl : Z}.
(* the donor's Section hypotheses this stretch uses (W_relay_add_cut.v's list, in its order), converted to ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HH28 : VAL (A_HI 28) + RA_HI_NSRC = rg_nsrc RG.
Hypothesis HH30 : VAL (A_HI 30) + RA_HI_SRC = rg_src RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
(* the memset intrinsic over ARx (W_sites_x.v; keeps ly S Hp) *)
Hypothesis AMEMSET : aintrin_realizes_x SEGS B ARx OSet (SIGMA WS_asan_memset).
(* the conversion's own: no hidden head in any ARx state (a Theorem Labs lane's ruling; the table block's shadow is
   W_journal_x's range_addressable_of_block_hp0_x / shadow_hull_vis_of_block_hp0_x), and W_kit_x.v Section g's IMGC /
   BLKN (image B's band, as W_kit_x.v and W_kit_xb.v state them), for blk_off_imgB_x *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.

(* the live blocks are pairwise distinct (W_relay_add_app.v ra_nodup over ARx: alx_sep, and BLKN for their sizes) *)
Lemma ra_nodup_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR. destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. pose proof (BLKN ly S Hp W mem md p n HAR Hin) as Hn.
  cbn [snd]. pose proof (req_size_pos n Hn). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hpw Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this segment at a world relation R, over the cut interface's R forms
   (W_relay_add_cut_x.v Section cR): its runs and branches at their G twins and its memset call by its R call step
   (aj_gx_entry_at_xR).  At the cf instance R := wle' SEGS RZ_cf. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
Theorem pb_rb_app_xR : rb_app_stmtR B PST ARx MT RP G RG CTX R.
Proof.
intros cx W1 c1 HB HA KU.
destruct HA as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & T1 & -> & HRH & R19 & R20 & Hfd & HAL & HREL & HML & HRM1
  & HBLK).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAL as (HJ & HROM1 & HPK1 & HSV & HLK & HWAKE & HFR & HERR1).
pose proof HRH as (HRB & R8 & R18).
pose proof HREL as (Ms & Ws & Mn & Wn & Mc & Wc & Hlen16 & HTin & (tail & Htab) & Hents & HNDfd & HNOTAB).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 T1 ATABLE HAR HTin)
  as (HT16 & HT4096 & HTceil & HTapp & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTpres, HTapp.
pose proof HB as (HPRE & Hal32 & HCNT & H10 & Hfdr & HLOCK0 & HWAKE0 & HROM0 & HREL0 & HNEW & HGin & HGerr & HLIVE
  & HCTX & HMOK & HRM0 & HPK0).
destruct (HNEW Hfd) as (Hlt4 & HnotIn).
set (n := Z.of_nat (length (bxes cx))) in *.
assert (Hn03 : 0 <= n <= 3) by (unfold n; lia).
assert (RA : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (T1 + AENT * n) 8).
{ apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 T1 ATABLE (T1 + AENT * n) 8 HAR
    HTin);
  change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia. }
(* the seat (W_relay_add_app.v ra_app_seat, AR-free): its placement premises are this Section's HV4 / HV5 / HH28 /
   HH30 / HRGP, discharged by assumption *)
pose proof (ra_app_seat RG) as SEAT.
repeat match type of SEAT with ?P -> ?Q => specialize (SEAT ltac:(assumption)) end.
destruct (SEAT W1 regs1 m1 T1 n R18 R19 R20 Hn03 HT4096 HT16
  ltac:(unfold ATABLE in *; lia) HTapp Mn Ms RA) as [HS SHOK].
clear SEAT.
remember (Eimg (Ereg regs1 (ra_app_extra n T1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (ra_app_extra n T1)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs1 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs1 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs1 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = w64 (bxfd cx)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 n)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 T1)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (T1 + AENT * n))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE EEo.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal160 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HRB as (HspR & HgpR & HtpR & H23 & H24 & H25 & H26 & H27).
(* the table block is off image B (W_kit_xb.v blk_off_imgB_x: below 0x10000 or at / above 0x5fc000) *)
pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly1 S1 Hp1 W1 m1 md1 T1 ATABLE HAR HTin) as HToff.
change (req_size ATABLE) with 896 in HToff.
set (X := T1 + AENT * n) in *.
assert (HXv : X = T1 + 56 * n) by reflexivity.
unfold cfg_at. change (w64 (BASE + A_ra_app)) with (Z_to_bv 64 (BASE + A_ra_app)).
(* ---- 0x82b90 -> the trap edge 0x82bc4.  The loads s5 = |es| (atom 32: its range [0, 3] makes the lw's sign
   extension the identity) and s4 = T1 (atom 33); s1 = s4 + 56 s5 is atom 34 by the seat's alias.  TRAP 0x82bb0
   (`snez a0,s4; seqz a1,s1; beq a0,a1`) is decided inside this run: snez = 1 (atom 33 >= 4096), seqz = 0 (atom 34
   >= 4096). *)
paj_run_tok_xR RUNR HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
ra_mem Em1.
(* TRAP 0x82bc4 (`slti a0,s5,0; sltu a1,s1,s4; xor; xori 1; beqz`, pointer overflow): left open by the runner (s1 and
   s4 are distinct atoms); the taken arm is refuted by W_traps.v trap_ptr_sovf, both compares 0: slti (folded to 0
   by the runner from atom 32's range) and sltu s1,s4 (trap_U_sltu_ge: T1 <= T1 + 56 |es|). *)
psrr_branch_tok RUNR BRR HS SHOK Bspan.
{ exfalso. rewrite (trap_ptr_sovf E (SAlu ALU_SLTU (SOff 34 0) (SOff 33 0)) (SLit 0) 0) in Hc; [discriminate Hc | |].
  - apply (trap_U_sltu_ge E (SOff 33 0) (SOff 34 0) T1 X);
    [apply (U_atom E 33 T1 E33) | apply (U_atom E 34 X E34) |]; unfold AENT in *; lia.
  - rewrite U_SLit. reflexivity. }
(* ---- -> the call to __asan_memset (s1, 0, 56) at 0x82bd4 *)
paj_run_tok_xR RUNR HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
ra_mem Em2. rewrite Em1 in Em2. rewrite Em2 in HJ.
pmkst HS. rewrite Em2.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
lazymatch type of HS with context [restrict _ ?m] => set (msA := m) in * end.
assert (HSP1 : spZ (ms_regs msA) = bsp0 cx + -64).
{ change (spZ (ms_regs msA)) with (bv_unsigned (getr (ms_regs msA) 2)). rewrite P2, E2.
  change (bv_unsigned (getr regs1 2)) with (spZ regs1). rewrite HspR. unfold RA_FRAME. lia. }
assert (HSTKX : alloc_ceiling + RA_STK <= bsp0 cx) by (unfold bsp0; lia).
unfold RA_STK, RA_FRAME, ASTACK in HSTKX.
(* the slot's 56 bytes: in the table's block, a byte the journal may write (the footprint ra_FP when the table
   existed at the entry, else a block the entry did not have) *)
assert (AWRB : forall a, X <= a < X + 56 ->
  awr_byte RA_STK (bsp0 cx) (bFP cx) (ablocks B (bxly cx) (bxS cx)) (ablocks B ly1 S1) ly1 [] a).
{ intros a Ha. unfold awr_byte.
  destruct HBLK as [(HT0 & HPm) | (HT0 & HT1e & HBe)].
  - right; right; left. exists T1, ATABLE. split; [exact HTin|].
    split; [|change (req_size ATABLE) with 896; unfold AENT in *; lia].
    intros Hin0. pose proof (ra_nodup_x ly1 S1 Hp1 W1 m1 md1 HAR) as ND.
    apply (Permutation_NoDup HPm) in ND. inversion ND as [|? ? Hni _]. exact (Hni Hin0).
  - right; left. split.
    + unfold bFP, ra_FP. rewrite (proj2 (Z.eqb_neq _ 0) HT0).
      exists (bxT cx + AENT * n, bxT cx + AENT * (n + 1)).
      split; [left; reflexivity | cbn [fst snd]; rewrite <- HT1e; unfold AENT in *; lia].
    + exists T1, ATABLE. split; [exact HTin | change (req_size ATABLE) with 896; unfold AENT in *; lia]. }
assert (HDEST : dest_ok SEGS B ly1 S1 W1 (ms_regs msA) m1 X 56).
{ intros a Ha. destruct (HTpres a ltac:(unfold AENT in *; lia)) as [Hp Hno].
  split; [exact (apresent_writable SEGS (w_H W1) m1 a Hp)|]. split; [exact Hno|].
  rewrite HSP1. unfold ESTACK, AENT in *. lia. }
assert (HAMR : amem_range X 56).
{ unfold amem_range. unfold in_app in HTapp. unfold kLowShadowBeg, ASAN_CEIL in HTapp.
  rewrite C3, C4, C5. rewrite C3 in HTapp. unfold AENT in *. lia. }
pose proof (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 T1 ATABLE X 56 HAR HTin
  ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia)) as HRAX.
pose proof (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 T1 ATABLE X 56 HAR HTin
  ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia) ltac:(lia)) as HHULL.
(* __asan_memset (s1, 0, 56): AMEMSET through aj_gx_entry_at_xR, 64 bytes below the entry sp, returning to 0x82bd8
   (listing offset 2196) *)
eapply (SRrG_bind SEGS R R_trans).
{ apply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (RA_G RG) 0 [] ESTACK (SIGMA WS_asan_memset) (fun a => X <= a < X + 56)
    (fun _ mem' => forall i, 0 <= i < 56 -> aview SEGS (w_H W1) mem' (X + i) = Some 0)
    W1 (ms_regs msA) m1 RA_STK (bsp0 cx) (bFP cx) (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx) []
    ly1 S1 Hp1 _ k1 (-64) (Z_to_bv 64 (BASE + 2196)) HG eq_refl HJ HSP1 eq_refl ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(unfold RA_STK, RA_FRAME, ASTACK, ESTACK; lia)).
  - rewrite P3, E3, HgpR. exact Hgp0.
  - rewrite P4, E4, HtpR. exact Htp0.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_le_gt_dec X a) as [H1 | H1];
    [destruct (Z_lt_ge_dec a (X + 56)) as [H2 | H2]; [left; lia | right; lia] | right; lia].
  - intros a Ha Hga. exfalso. pose proof (pa_img_range a (proj1 (HG a Hga))). unfold AENT in *. lia.
  - intros a Ha _. split; [exact (AWRB a Ha) | lia].
  - intros HPREc _. eapply SRr_mono.
    { exact (AMEMSET ly1 S1 Hp1 W1 (ms_regs msA) m1 _ X 0 56 HPREc
        ltac:(rewrite P10, E34; reflexivity) ltac:(rewrite P11; reflexivity) ltac:(rewrite P12; reflexivity)
        ltac:(lia) ltac:(unfold AENT in *; lia) ltac:(unfold AENT in *; lia) HDEST HAMR
        (fun a Ha => kept_x_off_img SEGS B a (fun Hi => ltac:(pose proof (pa_img_range a Hi); unfold AENT in *; lia)))
        HRAX (fun _ => HHULL) I). }
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP' & Hs' & _ & Hset & Hfr & Hpr).
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HAR'|]. split; [exact HP'|].
    split; [exact Hs'|]. split; [intros i Hi; rewrite (Hset i Hi); reflexivity|]. split; [exact Hfr | exact Hpr]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HZ2 & HFR2 & HPR2).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
(* ---- back at 0x82bd8: a fresh symbolic memory (the two loads are done); the callee-saved registers kept *)
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall i, (i < 35)%nat -> ew Ea i = ew E i)
  by (intros i Hi; rewrite HEa; apply YN3v.ew_havoc_old; exact Hi).
assert (HAEa : env_agree 32 (Ereg regs1 (ra_app_extra n T1)) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (U34a : bv_unsigned (ew Ea 34) = X)
  by (rewrite OLDa by lia; rewrite E34; apply unsigned_lit_small; unfold AENT in *; lia).
assert (U308a : bv_unsigned (ew Ea 308) = rg_nsrc RG - 484).
{ rewrite (HEIa 308%nat ltac:(cbv; lia)). change (A_HI 28) with 308%nat in HH28. unfold RA_HI_NSRC in HH28. lia. }
pose proof (pa_obj_img 4 ltac:(lia)) as HI4. rewrite HV4 in HI4.
(* what memset kept: the globals (image bytes, off the slot and off its scratch) *)
assert (GIMG : forall a, inG (RA_G RG) a -> 0x10000 <= a < 0x5fc000)
  by (intros a Ha; exact (pa_img_range a (proj1 (HG a Ha)))).
assert (GKM : forall a, inG (RA_G RG) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. pose proof (GIMG a Ha). apply HFR2; [lia | unfold AENT in *; lia | unfold ESTACK in *; lia]. }
assert (WN2 : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W1) mem2) (rg_nsrc RG + o)).
{ intros o Ho. pose proof (ra_nsrc_in RG (rg_nsrc RG + o) ltac:(lia)) as Hin. pose proof (GIMG _ Hin).
  destruct (aview SEGS (w_H W1) m1 (rg_nsrc RG + o)) as [v|] eqn:Ev;
  [| exfalso; exact (ra_view_some (w_H W1) m1 (rg_nsrc RG) 4 n o Mn ltac:(cbn; lia) Ev)].
  apply (ra_writable_view (w_H W1) mem2 (rg_nsrc RG + o) v ltac:(lia));
  [rewrite (GKM _ Hin); exact Ev | exact (HNROM _ Hin)]. }
(* the two cells the stretch stores to: g_nsrc through the auipc atom (offset 484), the slot's fd field *)
assert (RN : region_ok SEGS Ea (mrestrict (w_H W1) mem2) ra_nsrc_w).
{ unfold region_ok, ra_nsrc_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U308a. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace (rg_nsrc RG - 484 + o) with (rg_nsrc RG + (o - 484)) by lia. apply WN2. lia. }
pose proof (st_ok_pi_add_region Ea _ _ ra_nsrc_w HS ltac:(vm_compute; reflexivity) RN I) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (RS : region_ok SEGS Ea (mrestrict (w_H W1) mem2) ra_slot_w).
{ unfold region_ok, ra_slot_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U34a. split; [unfold AENT in *; lia|]. split; [unfold AENT in *; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HPR2. apply HTpres. unfold AENT in *. lia. }
assert (RSD : extent_disjoint Ea ra_slot_w ra_nsrc_w).
{ unfold extent_disjoint, ra_slot_w, ra_nsrc_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U34a, U308a. unfold AENT in *. lia. }
pose proof (st_ok_pi_add_region Ea _ _ ra_slot_w HS ltac:(vm_compute; reflexivity) RS (conj RSD I)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (SHOK2 : sh_ok SEGS Bx ra_app_SH Ea (mrestrict (w_H W1) mem2)).
{ assert (HBxa : U Ea Bx = SHADOW_OFF)
    by (unfold Bx; rewrite (U_atom Ea 18 SHADOW_OFF ltac:(rewrite OLDa by lia; exact E18)) by (unfold SHADOW_OFF; lia);
        reflexivity).
  unfold sh_ok, ra_app_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea Bx 34 X 8 X 0 8
    (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mem2 md2 T1 ATABLE X 8 HAR2 HTin
      ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia)) HBxa);
  [rewrite (U_atom Ea 34 X ltac:(rewrite OLDa by lia; exact E34)) by (unfold AENT in *; lia); reflexivity | lia | lia |].
  intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
(* ---- 0x82bd8 -> 0x82c04 in one run.  TRAP 0x82bdc (`addiw a0,s5,1; blt a0,s5`) is decided inside it (a0 = atom 32
   plus 1 against atom 32, range [0, 3]); `sw a0,484(s3)`: g_nsrc = |es| + 1; TRAP 0x82be4 (`beqz s4`) decided (atom 33
   >= 4096); TRAP 0x82bec (`andi a0,s1,7; bnez`) decided (atom 34 8-aligned); the shadow check of s1 decided by the
   shadow entry over the slot (its slow path 0x82c84 and the error path 0x82c90 are not reached); `sw s0,0(s1)`. *)
paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 Bspan A_ra_unlock.
{ apply awr_ok_x_cons.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U34a in Ha.
    left. split; [exact (AWRB a ltac:(unfold AENT in *; lia)) | lia].
  - apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U308a in Ha.
    apply (ra_nsrc_in RG). lia. }
lazymatch type of HS with context [restrict _ ?m] => set (msC := m) in * end.
lazymatch goal with Hx : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem msC)) |- _ => rename Hx into HFrC end.
lazymatch goal with Hx : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem msC)) |- _ => rename Hx into HGrC end.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARC.
assert (Hn' : n = Z.of_nat (length (bxes cx))) by reflexivity.
(* what the run kept: every byte off its two store cells *)
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (X <= a < X + 4) ->
  aview SEGS (w_H W1) (ms_mem msC) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha H1 H2. apply (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msC) HFrC a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U34a, ?U308a in Hr; lia | ]).
  destruct Hin. }
(* ... and from RBAR: every byte off g_nsrc, the slot and memset's scratch *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (X <= a < X + 56) ->
  ~ (bsp0 cx + -64 - ESTACK <= a < bsp0 cx + -64) ->
  aview SEGS (w_H W1) (ms_mem msC) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 ltac:(lia)). exact (HFR2 a Ha H2 H3). }
assert (GW : forall a, inG (RA_G RG) a -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> aview SEGS (w_H W1) m1 a <> None ->
  abyte_kept W1 m1 W1 (ms_mem msC) a).
{ intros a Hg Hn Hv. pose proof (GIMG a Hg).
  apply ra_abyte_kept; [lia | | exact Hv | exact (HNROM a Hg)].
  apply KALL; [lia | exact Hn | intros Hs; destruct HToff; unfold AENT in *; lia | unfold ESTACK in *; lia]. }
assert (KTB : forall b, T1 <= b < T1 + 896 -> ~ (X <= b < X + 56) ->
  aview SEGS (w_H W1) (ms_mem msC) b = aview SEGS (w_H W1) m1 b).
{ intros b Hb Hs. apply KALL; [lia | intros Hn; destruct HToff; lia | exact Hs | unfold ESTACK in *; lia]. }
assert (KBK : forall p mm b, In (p, mm) (ablocks B ly1 S1) -> p <= b < p + req_size mm -> ~ (X <= b < X + 56) ->
  aview SEGS (w_H W1) (ms_mem msC) b = aview SEGS (w_H W1) m1 b).
{ intros p mm b Hpm Hb Hs.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p mm HAR Hpm) as (_ & Hp4 & Hpc & _).
  pose proof (blk_off_imgB_x B ARx LAWS IMGC BLKN ly1 S1 Hp1 W1 m1 md1 p mm HAR Hpm) as Hpo.
  apply KALL; [lia | intros Hn; destruct Hpo; lia | exact Hs | unfold ESTACK in *; lia]. }
(* the two stores, read back from the run's regions *)
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRGs.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRGn.
cbn [ms_mem restrict] in HRGs, HRGn.
assert (VFD : val_mem SEGS (mrestrict (w_H W1) (ms_mem msC)) X 4 (bxfd cx)).
{ pose proof (field_of_region Ea _ 34%nat X _ 0 4 0 4 0 4%N (SOff 8 0) (bxfd cx) HRGs U34a (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite OLDa by lia; rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (VNS : val_mem SEGS (mrestrict (w_H W1) (ms_mem msC)) (rg_nsrc RG) 4 (n + 1)).
{ pose proof (field_of_region Ea _ 308%nat (rg_nsrc RG - 484) _ 484 488 484 488 484 4%N (SOff 32 1) (n + 1) HRGn U308a
    (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite OLDa by lia; rewrite E32, unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv.
  replace (rg_nsrc RG - 484 + 484) with (rg_nsrc RG) in Hv by lia. exact Hv. }
assert (WNC : awr W1 (ms_mem msC) (rg_nsrc RG) 4).
{ pose proof HRGn as HRGn'. unfold region_ok in HRGn'.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRGn'.
  destruct HRGn' as (_ & _ & HWn & _). rewrite U308a in HWn.
  intros i Hi. unfold arm. replace (rg_nsrc RG + i) with (rg_nsrc RG - 484 + (484 + i)) by lia. apply HWn. lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 18; 23; 24; 25; 26; 27]%bv HS HAEa
  ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) m1 a <> None).
{ intros a Ha. destruct HLK as (V0 & V4 & V8 & _).
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [|destruct (Z_lt_ge_dec a (rg_lock RG + 8))].
  - replace a with (rg_lock RG + (a - rg_lock RG)) by lia.
    exact (ra_view_some _ _ (rg_lock RG) 4 _ (a - rg_lock RG) V0 ltac:(cbn; lia)).
  - replace a with (rg_lock RG + 4 + (a - rg_lock RG - 4)) by lia.
    exact (ra_view_some _ _ (rg_lock RG + 4) 4 _ (a - rg_lock RG - 4) V4 ltac:(cbn; lia)).
  - replace a with (rg_lock RG + 8 + (a - rg_lock RG - 8)) by lia.
    exact (ra_view_some _ _ (rg_lock RG + 8) 4 _ (a - rg_lock RG - 8) V8 ltac:(cbn; lia)). }
(* ---- RBUR at 0x82c04 *)
pmkst HS.
apply KU. unfold RBUR.
exists (ms_regs msC), ly1, S1, Hp1, (ms_mem msC). eexists. exists k1, T1.
split; [reflexivity|].
split; [unfold bregs_held, bregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
split; [exact Hfd|].
split.
{ split; [exact HJ2|].
  (* rom_view: a ROM byte is an image byte (pa_img_range), not g_nsrc (HNROM), off the heap slot (HToff) and below
     memset's scratch, so both runs and the memset keep its view *)
  split.
  { intros a Ha. rewrite <- (HROM1 a Ha). pose proof Ha as (sg & Hin & _ & Hr).
    pose proof (pa_img_range a (ex_intro _ sg (conj Hin Hr))) as Ra.
    apply KALL; [lia | intros Hn; exact (HNROM a (ra_nsrc_in RG a Hn) Ha)
      | intros Hs; destruct HToff; unfold AENT in *; lia | unfold bsp0, ESTACK in *; lia]. }
  split; [intros a Hi Ho He Hp; apply (apresent_grows _ _ _ a HGrC); apply HPR2; exact (HPK1 a Hi Ho He Hp)|].
  split.
  { intros i Hi. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem msC) _ 8 _); [|exact (HSV i Hi)].
    intros kk Hk. cbn in Hk. apply KALL; unfold bsp0, RA_FRAME, ESTACK, AENT in *; lia. }
  split.
  { apply (alock_at_kept RG W1 m1 W1 (ms_mem msC) true HLK).
    intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply GW; [exact (ra_lock_in RG a Ha) | ra_pick HRGP 2%nat 3%nat D23; lia | exact (LKV a Ha)]. }
  split.
  { unfold awake_at. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem msC) _ 4 _); [|exact HWAKE].
    intros kk Hk. cbn in Hk. destruct (HWK (rg_wake RG + 4 + kk) ltac:(lia)) as (Hi & _).
    pose proof (pa_img_range _ Hi). ra_pick HRGP 3%nat 6%nat D36.
    apply KALL; [lia | lia | intros Hs; destruct HToff; unfold AENT in *; lia | unfold bsp0, ESTACK in *; lia]. }
  split; [exact HFR|].
  (* errno's four bytes: image bytes below kLowMemEnd, none of RA_G (so not g_nsrc), off the heap slot and below
     memset's scratch: kept by both runs and by the memset *)
  eapply rb_errno_step; [exact HERR1|]. intros i Hi.
  assert (EL : 0 <= as_errno B + i < kLowMemEnd /\ in_img SEGS (as_errno B + i)) by (eapply ra_errno_low; eassumption).
  assert (EN : ~ inG (RA_G RG) (as_errno B + i)) by (eapply rb_errno_notG; eassumption).
  destruct EL as [_ Himg]. pose proof (pa_img_range _ Himg).
  apply KALL; [lia | intros Hn; exact (EN (ra_nsrc_in RG _ Hn)) | intros Hs; destruct HToff; unfold AENT in *; lia
    | unfold bsp0, ESTACK in *; lia]. }
split.
{ assert (KS : forall x, rg_src RG <= x < rg_src RG + Z.of_nat 8 -> abyte_kept W1 m1 W1 (ms_mem msC) x).
  { intros x Hx. cbn in Hx. apply GW; [exact (ra_src_in RG x Hx) | ra_pick HRGP 3%nat 5%nat D35; lia |].
    replace x with (rg_src RG + (x - rg_src RG)) by lia.
    exact (ra_view_some _ _ (rg_src RG) 8 _ (x - rg_src RG) Ms ltac:(cbn; lia)). }
  assert (KC : forall x, rg_capsrc RG <= x < rg_capsrc RG + Z.of_nat 4 -> abyte_kept W1 m1 W1 (ms_mem msC) x).
  { intros x Hx. cbn in Hx. apply GW; [exact (ra_capsrc_in RG x Hx) | ra_pick HRGP 3%nat 4%nat D34; lia |].
    replace x with (rg_capsrc RG + (x - rg_capsrc RG)) by lia.
    exact (ra_view_some _ _ (rg_capsrc RG) 4 _ (x - rg_capsrc RG) Mc ltac:(cbn; lia)). }
  assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (bxes cx)).
  { eapply Forall_impl; [|exact Hents]. intros e (_ & _ & EP1 & EP2 & _). split; assumption. }
  assert (HPADS2 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
    (bxes cx ++ [ra_new (bxfd cx)])).
  { apply Forall_app. split; [exact HPADS | constructor; [split; reflexivity | constructor]]. }
  pose proof (ra_concat_len _ HPADS) as HCL.
  destruct Htab as (Tl1 & Tl2 & Tg). unfold ATABLE, AENT in Tl1.
  assert (HTL : (56 <= length tail)%nat) by lia.
  rewrite <- (firstn_skipn 56 tail) in Tg. unfold bzs in Tg. rewrite !map_app in Tg.
  apply garr8_app in Tg as [GCE Tg]. apply garr8_app in Tg as [_ GTL].
  rewrite !length_map, HCL, length_firstn in GTL.
  replace (T1 + Z.of_nat (56 * length (bxes cx)) + Z.of_nat (Nat.min 56 (length tail))) with (X + 56) in GTL by lia.
  unfold arelay_at.
  split; [exact (akept_vm W1 m1 W1 (ms_mem msC) (rg_src RG) 8 T1 KS Ms)|].
  split; [exact (akept_awr W1 m1 W1 (ms_mem msC) (rg_src RG) 8 (fun x Hx => KS x ltac:(cbn; lia)) Ws)|].
  split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact VNS|].
  split; [exact WNC|].
  split; [exact (akept_vm W1 m1 W1 (ms_mem msC) (rg_capsrc RG) 4 16 KC Mc)|].
  split; [exact (akept_awr W1 m1 W1 (ms_mem msC) (rg_capsrc RG) 4 (fun x Hx => KC x ltac:(cbn; lia)) Wc)|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [exact HTin|].
  split.
  { exists (skipn 56 tail). unfold atable_at.
    split; [rewrite length_skipn, length_app; cbn [length]; unfold ATABLE, AENT; lia|].
    split; [rewrite length_app, (ra_concat_len _ HPADS2), length_skipn, length_app; cbn [length]; unfold ATABLE; lia|].
    rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
    unfold bzs. rewrite !map_app, <- app_assoc.
    apply garr8_app. split.
    { apply (ra_garr8_kept (w_H W1) (w_H W1) m1 (ms_mem msC) T1 _ GCE).
      intros b Hb. rewrite length_map, HCL in Hb. apply KTB; lia. }
    rewrite length_map, HCL. replace (T1 + Z.of_nat (56 * length (bxes cx))) with X by lia.
    apply garr8_app. split.
    { rewrite ra_new_bytes. apply garr8_app. split.
      - rewrite ra_le4_bytes by lia. exact (ra_le_garr8 _ X 4 (bxfd cx) VFD ltac:(cbn; lia)).
      - rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.
        apply ra_garr8_zeros. intros j Hj. cbn in Hj.
        rewrite (KR2 (X + Z.of_nat 4 + j) ltac:(lia) ltac:(intros Hs; destruct HToff; lia) ltac:(lia)).
        replace (X + Z.of_nat 4 + j) with (X + (4 + j)) by lia. apply HZ2. lia. }
    rewrite length_map, (ra_eb_len (ra_new (bxfd cx)) eq_refl eq_refl).
    replace (X + Z.of_nat 56) with (X + 56) by lia.
    apply (ra_garr8_kept (w_H W1) (w_H W1) m1 (ms_mem msC) (X + 56) _ GTL).
    intros b Hb. rewrite length_map, length_skipn in Hb. apply KTB; lia. }
  split.
  { apply Forall_app. split.
    - rewrite Forall_forall in Hents |- *. intros e He.
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msC) e (Hents e He)).
      + intros r Hr a Ha.
        destruct (ra_efp_in_block B ly1 S1 W1 m1 e (Hents e He) r a Hr Ha) as (p & mm & Hpm & Hpa).
        pose proof (ra_efp_off_slot_x B ARx RG LAWS ly1 S1 Hp1 W1 m1 md1 T1 (bxes cx) HAR HREL ltac:(lia) e r a He Hr Ha)
          as Hsl.
        change (Z.of_nat (length (bxes cx))) with n in Hsl.
        split; [apply (KBK p mm a Hpm Hpa); unfold AENT in *; lia|].
        intros _. destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 (ms_mem msC) _ p mm HARC Hpm) as (_ & _ & _ & _ & HpC & _).
        exact (apresent_writable SEGS _ _ a (proj1 (HpC a Hpa))).
      + exact (ra_eblks_in B ly1 S1 W1 m1 e (Hents e He)).
    - constructor; [apply ra_new_ok; lia | constructor]. }
  split.
  { rewrite map_app. cbn [map re_fd ra_new]. apply NoDup_ListNoDup.
    apply (Permutation_NoDup (Permutation_app_comm [bxfd cx] (map re_fd (bxes cx)))).
    cbn [app]. constructor; [exact HnotIn | apply NoDup_ListNoDup; exact HNDfd]. }
  (* arelay_at's 12th conjunct (W_rep.v:170, no entry's block is the table block): the old entries by RBAR's arelay_at
     at the same table T1 (HNOTAB), the new entry owns no block (ra_new: cap 0, held array 0, no keys) *)
  apply Forall_app. split; [exact HNOTAB|].
  constructor; [|constructor]. intros b Hb. cbn in Hb. destruct Hb. }
split; [exact HML|].
(* the room: RBAR's budget, the allocator state S1 unchanged *)
split; [exact HRM1 | exact HBLK].
Qed.
End cR.
(* the strict segment is its R twin at R := wle (route R's rule: one walk text) *)
Theorem pb_rb_app_x : rb_app_stmt B PST ARx MT RP G RG CTX.
Proof.
eapply (pb_rb_app_xR (@wle SEGS));
  first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Qed.
End c.
End b.
End a.
