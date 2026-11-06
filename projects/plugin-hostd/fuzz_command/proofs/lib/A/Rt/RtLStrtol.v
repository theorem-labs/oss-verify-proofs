(* Our runtime contract for the strtol interceptor: astrtol_realizes (RtNumber.v) at 0x451e0, the one-instruction
   trampoline `j 0x4d048` (the image's objdump listing, line 18800), with the stack-protector pair 0xa7098 -> 0x6045d8 that
   musl's strtol reads. The walk is A/Bz/A/I_strtolw.v istrtol_spec, which starts AT the trampoline (its first step
   is the jump, so A/Bz/A/I_tramp.v tramp_strtol is not needed here) and runs the interceptor body 0x4d048, musl's
   strtol through the slot 0xa8288 and the *endptr fix-up StrtolFixAndCheck 0x57168 (A/Bz/A/I_strtolfix.v
   sfixE_spec) to the return. Its two Section hypotheses are discharged by A/Bz/A/R_isPoisoned.v rip_proof (the
   range check) and A/Prog/strtol_wrap_sb.v sb_proof (musl's strtol at 0x9e984).
   - pre side: RtBzAdapt.v turns our premises into the walk's (stack window, string, guard pair, range checks,
     separation from the callee's window) and RtBzClean.v moves them to the cleaned store. The end pointer's cell:
     its eight bytes lie outside the image (the contract's ly_img premise), so no segment supplies them and
     awrite_ok's writable_at makes each one a byte of the store; the cleaned store keeps them (Dc is false there).
     The errno cell: the walk names it tp - 164, our contract as_errno B; CmdBSyms gives as_tp B = TFIB_TP and
     as_errno B = TFIB_ERRNO = TFIB_TP - 164 (A/AF0m.v:13,18), and ecall_pre gives tp = as_tp B. The interceptor's
     fixed cells (the slots 0xa8288 and 0xa63e8, the flag byte 0xae8b8 + 29, the asan-inited byte 0xb1d98 and
     I_strtolfix.v icells_sx) are read from the record's constant table, as RtLStrncmp.v reads the strncmp
     interceptor's.
   - post side: the walk writes its stack window, the end pointer's cell and the errno cell, so
     RtBzAdaptP.art_post_clean gives our art_post with E = the endptr cell and the errno cell; each written byte is
     read off the walk's rw_cells post.
   - the answer: the walk returns lib/A/Prog/__intscan_c.v's s10_val / s10_end / s10_errno, the contract states
     lib/Prog/__intscan_c.v's; the two files state the same definitions over the same CType (s10_*_same). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YK14 YK1b YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d
YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import
RtDefs RtNumber RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2y.
From OSSVerify.plugin_hostd.fuzz_command.images Require Asan.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.CType.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.__intscan_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__intscan_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolfix.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol_wrap_sb.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LPIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.__intscan_c.
Module LCT := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.CType.
Module APIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.__intscan_c.
Module SW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolw.
Module SFX := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strtolfix.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Module SBP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strtol_wrap_sb.

(* ---- the walk's answer and the contract's: the same definitions ---- *)

Lemma s10_val_same : forall s, APIS.s10_val s = LPIS.s10_val s.
Proof. intros s. reflexivity. Qed.

Lemma s10_end_same : forall s, APIS.s10_end s = LPIS.s10_end s.
Proof. intros s. reflexivity. Qed.

Lemma s10_errno_same : forall s w, APIS.s10_errno s w = LPIS.s10_errno s w.
Proof. intros s w. reflexivity. Qed.

(* the end the walk returns lies inside the string (lib/Prog/number.v:20-65, end_le) *)
Lemma ndig_le : forall l, (LPIS.ndig l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [LPIS.ndig length]; [lia|]. destruct (LCT.c_digit b); lia. Qed.

Lemma skip_le : forall l, (length (LCT.skip_space l) <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [LCT.skip_space length]; [lia|]. destruct (LCT.c_space b); cbn [length]; lia. Qed.

Lemma rest_le : forall s, (length (LPIS.s10_rest s) <= length s)%nat.
Proof.
  intros s. unfold LPIS.s10_rest. pose proof (skip_le s) as H.
  destruct (LCT.skip_space s) as [|b r]; cbn [LPIS.sign_split]; [cbn [snd length]; lia|].
  cbn [length] in H. destruct (bv_unsigned b =? 45); [cbn [snd]; lia|].
  destruct (bv_unsigned b =? 43); cbn [snd length]; lia.
Qed.

Lemma end_le : forall s, 0 <= LPIS.s10_end s <= Z.of_nat (length s).
Proof.
  intros s. pose proof (rest_le s) as R. pose proof (ndig_le (LPIS.s10_rest s)) as N.
  unfold LPIS.s10_end, LPIS.s10_nd. destruct (Nat.eqb (LPIS.ndig (LPIS.s10_rest s)) 0); lia.
Qed.

(* ---- byte arithmetic ---- *)

Lemma u8mod : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity. Qed.

(* a byte of a little-endian word does not see the bits above it *)
Lemma shr_mod_low : forall z n j, 0 <= j -> j + 8 <= n ->
  Z.shiftr (z mod 2 ^ n) j mod 256 = Z.shiftr z j mod 256.
Proof.
  intros z n j Hj Hn. change 256 with (2 ^ 8).
  rewrite <- (Z.land_ones (Z.shiftr (z mod 2 ^ n) j) 8), <- (Z.land_ones (Z.shiftr z j) 8) by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  rewrite Z.testbit_ones by lia.
  destruct (Z.ltb_spec i 8) as [Hl|Hl]; [|rewrite !andb_false_r; reflexivity].
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma le_byte_wrap64 : forall z k, (k < 4)%nat ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 z)) (8 * Z.of_nat k) mod 256 = le_byte z 4 k.
Proof.
  intros z k Hk. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  unfold le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite !shr_mod_low by lia. reflexivity.
Qed.

Lemma le_byte_word : forall (w : word) k, (k < 4)%nat ->
  Z.shiftr (bv_unsigned w) (8 * Z.of_nat k) mod 256 = le_byte (bv_unsigned w) 4 k.
Proof.
  intros w k Hk. unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite shr_mod_low by lia. reflexivity.
Qed.

(* the contracts' band room keeps a range below 2^47 *)
Lemma amem_top : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

(* ---- reading words off the view ---- *)

Lemma rdword_ex : forall (rd : reader) a, (forall k, 0 <= k < 8 -> exists z, rd (a + k) = Some z) ->
  exists v, rdword rd a = Some v.
Proof.
  intros rd a H.
  destruct (H 0 ltac:(lia)) as (z0 & E0). rewrite Z.add_0_r in E0.
  destruct (H 1 ltac:(lia)) as (z1 & E1). destruct (H 2 ltac:(lia)) as (z2 & E2).
  destruct (H 3 ltac:(lia)) as (z3 & E3). destruct (H 4 ltac:(lia)) as (z4 & E4).
  destruct (H 5 ltac:(lia)) as (z5 & E5). destruct (H 6 ltac:(lia)) as (z6 & E6).
  destruct (H 7 ltac:(lia)) as (z7 & E7).
  unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.

Lemma view_of_store : forall (H : word -> bool) mem a b, mrestrict H mem (Z_to_bv 64 a) = Some b ->
  aview tfibsegs H mem a = Some (bv_unsigned b).
Proof. intros H mem a b E. unfold aview, mbyte. rewrite E. reflexivity. Qed.

(* eight bytes a walk leaves at [a], read through the view as a word *)
Lemma rdword_of_E : forall (H : word -> bool) (mem' m : word -> option byte) a v,
  0 <= v < 2 ^ 64 ->
  BM.bytes_at BI.asegs m a (BM.le8 (Z_to_bv 64 v)) ->
  (forall k, 0 <= k < 8 ->
     aview tfibsegs H mem' (a + k) = option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs m (BM.wa (a + k)))) ->
  rdword (aview tfibsegs H mem') a = Some v.
Proof.
  intros H mem' m a v Hv (_ & _ & HB) HR.
  apply (AF0x.val_mem_rdword H mem' a v Hv).
  intros k Hk.
  pose proof (HR (Z.of_nat k) ltac:(lia)) as E.
  rewrite (HB k ltac:(rewrite BM.length_le8; exact Hk)) in E.
  rewrite (RtBzPre.le8_nth v k Hv Hk) in E. cbn [option_map] in E.
  unfold aview in E.
  destruct (mbyte tfibsegs (mrestrict H mem') (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate E].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* four bytes a walk leaves at [a], read through the view as a 32-bit cell *)
Lemma rd32_of_E : forall (H : word -> bool) (mem' m : word -> option byte) a (w : word),
  BM.bytes_at BI.asegs m a (BM.le4 w) ->
  (forall k, 0 <= k < 4 ->
     aview tfibsegs H mem' (a + k) = option_map (fun b : byte => bv_unsigned b) (BM.mrd BI.asegs m (BM.wa (a + k)))) ->
  rd32 (aview tfibsegs H mem') a (bv_unsigned w).
Proof.
  intros H mem' m a w (_ & _ & HB) HR k Hk.
  rewrite (HR (Z.of_nat k) ltac:(lia)).
  rewrite (HB k ltac:(rewrite BM.length_le4; exact Hk)).
  unfold BM.le4. rewrite RtBzPre.nth_le_bytes by exact Hk. cbn [option_map].
  f_equal. rewrite u8mod. exact (le_byte_word w k Hk).
Qed.

(* ---- the image's span and the end pointer's cell ---- *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma img_lo_hi : forall ly S md, ALedger tfibsegs ly S md ->
  fst (ly_img ly) <= 0x10000 /\ 0x606000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
  intros ly S md L. split.
  - destruct (al_img _ _ _ _ L Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
  - destruct (al_img _ _ _ _ L Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.

Lemma not_img_of_out : forall ly S md a, ALedger tfibsegs ly S md -> ~ in_zr a (ly_img ly) -> ~ in_img tfibsegs a.
Proof.
  intros ly S md a L Hn (sg & Hsg & Ha). destruct (al_img _ _ _ _ L sg Hsg) as [I1 I2].
  apply Hn. unfold in_zr. lia.
Qed.

Lemma ro_off : forall a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> BM.ro_addr BI.asegs (BM.wa a) = false.
Proof.
  intros a Ha Hn. unfold BM.ro_addr. rewrite (BM.wa_unsigned a Ha).
  replace (find_segment BI.asegs a 1) with (@None Segment) by (symmetry; exact (AE2y.find_segment_none a Hn)).
  reflexivity.
Qed.

(* outside every segment a writable byte is a byte of the store *)
Lemma byte_of_writable_off : forall (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  writable_at tfibsegs m a -> exists b, m (Z_to_bv 64 a) = Some b.
Proof.
  intros m a Ha Hn Hw. unfold writable_at, wview in Hw.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply Hw. rewrite (unsigned_lit_small a Ha).
  replace (find_segment tfibsegs a 1) with (@None Segment) by (symmetry; exact (AE2y.find_segment_none a Hn)).
  reflexivity.
Qed.

(* the end pointer's word on the cleaned store, a cell the walk may write *)
Lemma ecell_clean : forall (W : world tfibsegs) mem e v, RtBzClean.rom_eq (mrestrict (w_H W) mem) ->
  0 <= e -> e + 8 <= 2 ^ 47 ->
  (forall a, e <= a < e + 8 -> writable_at tfibsegs (mrestrict (w_H W) mem) a /\ RtBzClean.Dc (BM.wa a) = false) ->
  rdword (aview tfibsegs (w_H W) mem) e = Some v ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) e [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros W mem e v RE He0 He8 HW RW.
  split.
  - split; [cbn; tauto|]. cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
    apply (RtBzClean.bytes_at_clean _ e _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia|].
    exact (RtBzAdapt.bz_bytes_of_rdword W mem e v RW He0 ltac:(lia)).
  - cbn [BC.cells_size BC.csize]. split; [exact He0|]. split; [lia|].
    intros i Hi. destruct (HW (e + i) ltac:(lia)) as (Hw & HD).
    rewrite (RtBzClean.wview_clean_nd _ _ HD). exact Hw.
Qed.

(* ---- the errno cell ---- *)

Lemma errno_img : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> in_img tfibsegs a.
Proof.
  intros a Ha. exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity|].
  cbn. unfold TFIB_ERRNO in Ha. lia.
Qed.

Lemma errno_not_static : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha HE. apply Exists_exists in HE as (r & Hr & Hz).
  assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst r))
                Tfib_owned_static = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C r Hr) as X. cbv beta in X.
  unfold in_zr in Hz. apply orb_true_iff in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma errno_dc : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> RtBzClean.Dc (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold TFIB_ERRNO in Ha; lia).
  apply RtBzClean.Dc_false; [apply RtBzClean.errno_not_ro; rewrite Hu; exact Ha |].
  rewrite Hu. unfold BM.UTOP, TFIB_ERRNO in *. lia.
Qed.

Lemma errno_seg : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> find_segment tfibsegs a 1 <> None.
Proof.
  intros a Ha HN.
  assert (Hb : match find_segment tfibsegs a 1 with Some _ => true | None => false end = true).
  { unfold TFIB_ERRNO in Ha.
    assert (E : a = 0x5e44f4 \/ a = 0x5e44f5 \/ a = 0x5e44f6 \/ a = 0x5e44f7) by lia.
    destruct E as [ E | [ E | [ E | E ] ] ]; rewrite E; vm_compute; reflexivity. }
  rewrite HN in Hb. discriminate.
Qed.

(* the errno cell lies in a segment, so the hidden set leaves it out *)
Lemma errno_wh : forall (W : world tfibsegs) a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a Ha. destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [|reflexivity].
  exfalso. apply (errno_seg a Ha).
  pose proof (w_Hoff W (Z_to_bv 64 a) EH) as X.
  rewrite unsigned_lit_small in X by (unfold TFIB_ERRNO in Ha; lia). exact X.
Qed.

(* the errno word on the cleaned store, a cell the walk may write *)
Lemma errno_cell_clean : forall (H : word -> bool) mem ev, RtBzClean.rom_eq (mrestrict H mem) ->
  rd32 (aview tfibsegs H mem) TFIB_ERRNO ev ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) TFIB_ERRNO [BC.C4 (Z_to_bv 64 ev)].
Proof.
  intros H mem ev RE HR.
  assert (C : BS.ro_cells BI.asegs (mrestrict H mem) TFIB_ERRNO [BC.C4 (Z_to_bv 64 ev)]).
  { split; [cbn; tauto|]. cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
    split; [unfold TFIB_ERRNO; lia|]. split; [rewrite BM.length_le4; unfold TFIB_ERRNO; lia|].
    intros i Hi. rewrite BM.length_le4 in Hi.
    destruct (AE2y.aview_byte_ex H mem _ _ (HR i Hi)) as (b & Hb & Hv & _).
    rewrite RtBzPre.mrd_mbyte, Hb. unfold BM.le4. rewrite RtBzPre.nth_le_bytes by exact Hi.
    f_equal. apply bv_eq. rewrite u8mod, <- Hv. symmetry. exact (le_byte_wrap64 ev i Hi). }
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
    [unfold TFIB_ERRNO; lia | cbn; unfold BM.UTOP, TFIB_ERRNO; lia | vm_compute; reflexivity |].
  apply rw_of_ro; [exact C | vm_compute; reflexivity].
Qed.

(* ---- the stack window: above the image, so a byte the walk leaves there is in the store ---- *)
Lemma win_in : forall (m : word -> option byte) (sp K lo : Z),
  BF.stk BI.asegs m lo sp -> lo <= sp - K -> TFIB_IMG_END <= lo ->
  forall a, sp - K <= a < sp -> m (Z_to_bv 64 a) <> None.
Proof.
  intros m sp K lo (Hlo & Hhi & ST) Hk Himg a Ha.
  destruct (ST a ltac:(lia)) as (_ & b & Hb). unfold BM.mrd, BM.wa in Hb.
  destruct (m (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
  assert (HN : BPE.seg_rom BI.asegs (Z_to_bv 64 a) = None) by exact (seg_rom_none_high a ltac:(lia)).
  rewrite HN in Hb. discriminate.
Qed.
End i.

(* ---- the strtol interceptor's fixed cells, read from the record's constant table ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

(* I_strtolfix.v:325 *)
Lemma icells_sx_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SFX.icells_sx (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. unfold SFX.icells_sx. split.
  - apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | c8 M].
  - apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | c1 M].
Qed.

(* the asan-inited byte 0xb1d98, written in place (I_strtolw.v:100) *)
Lemma inited_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xb1d98 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem RE M.
  assert (C : BS.rw_cells BI.asegs (mrestrict H mem) 0xb1d98 [BC.C1 (Z_to_bv 8 1)])
    by (apply rw_of_ro; [c1 M | vm_compute; reflexivity]).
  apply (RtBzClean.rw_cells_clean _ _ _ RE); [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact C].
Qed.

(* REAL(strtol)'s slot 0xa8288, the flag pointer 0xa63e8 and the replace_str flag byte (I_strtolw.v:101-102) *)
Lemma slots_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) -> ARm B ly S (aview tfibsegs H mem) ->
  BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xa8288 (BM.le8 (Z_to_bv 64 0x9e984)) /\
  BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xa63e8 (BM.le8 (Z_to_bv 64 0xae8b8)) /\
  BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xae8d5 [Z_to_bv 8 1].
Proof.
  intros ly S H mem RE M.
  assert (C1 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa8288 [BC.C8 (Z_to_bv 64 0x9e984)]) by c8 M.
  assert (C2 : BS.ro_cells BI.asegs (mrestrict H mem) 0xa63e8 [BC.C8 (Z_to_bv 64 0xae8b8)]) by c8 M.
  assert (C3 : BS.ro_cells BI.asegs (mrestrict H mem) 0xae8d5 [BC.C1 (Z_to_bv 8 1)]) by c1 M.
  pose proof (RtBzClean.ro_cells_clean (mrestrict H mem) 0xa8288 [BC.C8 (Z_to_bv 64 0x9e984)] RE
                ltac:(cbn; unfold BM.UTOP; lia) C1) as (_ & D1).
  pose proof (RtBzClean.ro_cells_clean (mrestrict H mem) 0xa63e8 [BC.C8 (Z_to_bv 64 0xae8b8)] RE
                ltac:(cbn; unfold BM.UTOP; lia) C2) as (_ & D2).
  pose proof (RtBzClean.ro_cells_clean (mrestrict H mem) 0xae8d5 [BC.C1 (Z_to_bv 8 1)] RE
                ltac:(cbn; unfold BM.UTOP; lia) C3) as (_ & D3).
  cbn [BC.cells_bytes BC.cbytes app] in D1, D2, D3. rewrite app_nil_r in D1, D2.
  split; [exact D1|]. split; [exact D2 | exact D3].
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Lemma errno_unowned : forall ly S (W : world tfibsegs) mem md a, AR tfibsegs B ly S W mem md ->
  TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
  intros ly S W mem md a HAR Ha Ho.
  apply (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR (errno_img a Ha))) in Ho.
  rewrite (ts_owned B TB) in Ho. exact (errno_not_static a Ha Ho).
Qed.

Theorem cmd_strtol : astrtol_realizes tfibsegs B 0x451e0 0xa7098 0x6045d8.
Proof.
  unfold astrtol_realizes.
  intros ly S W regs mem md x e str ev HG HPRE G10 G11 G12 Hx0 He0 SX HXL RDX AMX _ WR AME SEPXE SEPEERR
    EAL EOUT SEPXERR RDE HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & _ & _ & _ & _ & _ & G4).
  pose proof HAR as (_ & HLED & _).
  assert (EX : astr_len str = Z.of_nat (length str)) by reflexivity.
  pose proof (amem_top x _ AMX) as AMX'.
  pose proof (amem_top e _ AME) as AME'.
  pose proof (end_le str) as HEND.
  pose proof RDX as (_ & _ & HXN & _).
  pose proof WR as (_ & _ & _ & HWB & _).
  rewrite (ts_errno B TB) in SEPEERR, SEPXERR, RDE.
  (* 0. the end pointer's cell lies outside the image *)
  destruct (img_lo_hi ly S md HLED) as (IL & IH).
  assert (EOUT' : e + 8 <= 0x10000 \/ 0x606000 <= e).
  { destruct (Z_lt_le_dec e 0x10000) as [L1|L1].
    - destruct (Z_le_gt_dec (e + 8) 0x10000) as [L2|L2]; [left; exact L2|].
      exfalso. apply (EOUT 0x10000 ltac:(lia)). unfold in_zr. lia.
    - destruct (Z_lt_le_dec e 0x606000) as [L2|L2]; [|right; exact L2].
      exfalso. apply (EOUT e ltac:(lia)). unfold in_zr. lia. }
  assert (NIMG : forall a, e <= a < e + 8 -> ~ in_img tfibsegs a)
    by (intros a Ha; exact (not_img_of_out ly S md a HLED (EOUT a Ha))).
  assert (DCE : forall a, e <= a < e + 8 -> RtBzClean.Dc (BM.wa a) = false).
  { intros a Ha. apply RtBzClean.Dc_false; [exact (ro_off a ltac:(lia) (NIMG a Ha))|].
    rewrite BM.wa_unsigned by lia. unfold BM.UTOP. lia. }
  assert (RW0 : exists v0, rdword (aview tfibsegs (w_H W) mem) e = Some v0).
  { apply rdword_ex. intros k Hk.
    destruct (byte_of_writable_off (mrestrict (w_H W) mem) (e + k) ltac:(lia) (NIMG (e + k) ltac:(lia))
                (proj1 (HWB (e + k) ltac:(lia)))) as (b & Hb).
    exists (bv_unsigned b). exact (view_of_store (w_H W) mem (e + k) b Hb). }
  destruct RW0 as (v0 & RW0).
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  assert (ECELL : BS.rw_cells BI.asegs (clean (mrestrict (w_H W) mem)) e [BC.C8 (Z_to_bv 64 v0)]).
  { apply (ecell_clean W mem e v0 RE ltac:(lia) ltac:(lia)); [|exact RW0].
    intros a Ha. split; [exact (proj1 (HWB a Ha)) | exact (DCE a Ha)]. }
  pose proof (errno_cell_clean (w_H W) mem ev RE RDE) as ERRC.
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (3 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 3 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 3 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* 3. the string *)
  pose proof (RtBzAdapt.bz_str_bytes W mem x str SX ltac:(lia) ltac:(lia)) as BYXm.
  assert (BYX : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_clean _ x _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYXm]. }
  (* 4. the stack-protector pair musl's strtol reads *)
  destruct (RtBzAdapt.bz_guard_bytes W mem 0xa7098 0x6045d8 HG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (GOTm & can & CANm).
  assert (GOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0xa7098 (BM.le8 (Z_to_bv 64 0x6045d8))).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact GOTm]. }
  assert (CAN : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x6045d8 (BM.le8 can)).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact CANm]. }
  (* 5. the range checks: every prefix of the string with its NUL, and the end pointer's cell *)
  assert (CKX : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 ->
                  BQ.chk_ok (clean (mrestrict (w_H W) mem)) x nn).
  { intros nn Hnn. apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (3 * ESTACK) W regs mem x (astr_len str + 1) nn (astr_len str)
             RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKE : BQ.chk_ok (clean (mrestrict (w_H W) mem)) e 8).
  { apply (chk_ok_clean _ e _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_write B (3 * ESTACK) ly S W regs mem e 8 8 8 WR AME ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* 6. the string and the end pointer's cell lie outside the callee's window *)
  pose proof (RtBzAdapt.sep_of_read (3 * ESTACK) W regs mem x (astr_len str + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as SEPX.
  pose proof (RtBzAdapt.sep_of_write B (3 * ESTACK) ly S W regs mem e 8
                ltac:(unfold ESTACK; lia) ltac:(lia) WR) as SEPE.
  (* 7. the fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (inited_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as AI.
  pose proof (icells_sx_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICX.
  destruct (slots_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as (RSLOT & AFSLOT & AF29).
  (* 8. the registers the walk names *)
  assert (G4' : reg_get regs 4 = Z_to_bv 64 TFIB_TP) by (rewrite <- (ts_tp B TB); exact G4).
  assert (ETP : bv_unsigned (reg_get regs 4) = TFIB_TP)
    by (rewrite G4'; apply unsigned_lit_small; unfold TFIB_TP; lia).
  assert (ESP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 x) by exact G10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 e) by exact G11.
  assert (R12 : reg_get regs 12 = Z_to_bv 64 10) by exact G12.
  set (lo := spZ regs - 3 * ESTACK) in *.
  assert (Elo : lo = spZ regs - 12288) by (unfold lo, ESTACK; lia).
  assert (KH : BR.kHighShadowEnd < lo) by (unfold BR.kHighShadowEnd; lia).
  (* 9. the run *)
  eapply (bz_run_clean B TB W 0x451e0 regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - eapply RtBzAdaptP.evt_grows. apply bz_canon. rewrite R10, R11, R12.
    apply SW.istrtol_spec with (A := x) (Ep := e) (str := str)
      (fv := fun s => Z_to_bv 64 (APIS.s10_val s)) (fe := APIS.s10_end) (fr := fun s w => APIS.s10_errno s w)
      (ev := Z_to_bv 64 ev) (can := can) (e0 := Z_to_bv 64 v0) (lo := lo).
    + exact RIP.rip_proof.
    + exact SBP.sb_proof.
    + exact BYX.
    + lia.
    + lia.
    + lia.
    + exact EAL.
    + lia.
    + exact ECELL.
    + exact CKE.
    + rewrite ETP. exact ERRC.
    + exact GOT.
    + exact CAN.
    + rewrite ESP. exact ST.
    + rewrite ESP. unfold SW.ISTRTOL_DEPTH. lia.
    + exact KH.
    + rewrite ESP. exact Hsp47.
    + lia.
    + exact CKX.
    + rewrite ESP. destruct SEPX; lia.
    + rewrite ESP. destruct SEPE; lia.
    + rewrite ETP, ESP. left. unfold TFIB_TP. lia.
    + rewrite ETP. unfold TFIB_TP, TFIB_ERRNO in *. lia.
    + rewrite ESP. left. unfold SW.STRTOL_SSP_GOT. lia.
    + rewrite ESP. left. unfold SW.STRTOL_SSP_GUARD. lia.
    + rewrite ETP. right. unfold SW.STRTOL_SSP_GUARD, TFIB_TP. lia.
    + unfold SW.STRTOL_SSP_GUARD. destruct EOUT'; lia.
    + lia.
    + destruct EOUT'; lia.
    + exact M2S.
    + exact ICX.
    + exact AI.
    + exact MI.
    + exact RSLOT.
    + exact AFSLOT.
    + exact AF29.
    + exact HEND.
    + rewrite ETP. left. unfold TFIB_TP. lia.
    + rewrite ETP. right. unfold TFIB_TP. lia.
    + rewrite ETP. unfold TFIB_TP, TFIB_ERRNO in *. lia.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SW.istrtol_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI'
                    & ST' & CE & CR).
    cbv beta in CE, CR.
    rewrite ETP in MU, CR. rewrite ESP in MU, ST'.
    unfold SW.ISTRTOL_DEPTH in MU.
    apply (RtBzAdaptP.art_post_clean B LAWS (3 * ESTACK) 2272 ly S W regs mem md
             (fun a => (e <= a < e + 8) \/ aerrno_cell B a) _ msc ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm).
    all: subst msc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and E the walk kept the cleaned store *)
      intros y Hy HEy. apply MU. cbn [BF.outside].
      split; [exact Hy|]. split; [intros Hc; apply HEy; cbv beta; left; exact Hc|].
      split; [|exact I]. intros Hc. apply HEy. cbv beta. right. unfold aerrno_cell. rewrite (ts_errno B TB).
      unfold TFIB_ERRNO, TFIB_TP in Hc |- *. lia.
    + exact (win_in m' (spZ regs) 2272 lo ST' ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)).
    + exact GROW.
    + (* E: the end pointer's cell and the errno cell *)
      intros a [Ha|Ha].
      * destruct (HWB a Ha) as (HWa & HNo & _).
        split; [exact HNo|]. split; [lia|]. split; [exact (DCE a Ha)|].
        exact (RtBzAdapt.wH_false_of_writable W mem a HWa).
      * unfold aerrno_cell in Ha. rewrite (ts_errno B TB) in Ha.
        split; [exact (errno_unowned ly S W mem md a HAR Ha)|].
        split; [unfold TFIB_ERRNO in Ha; lia|].
        split; [exact (errno_dc a Ha) | exact (errno_wh W a Ha)].
    + (* the answer *)
      intros regs' mem' HR _ HE'. split; [|split].
      * rewrite (HR _). transitivity (Z_to_bv 64 (APIS.s10_val str)); [reflexivity|].
        unfold w64. rewrite s10_val_same. reflexivity.
      * apply (rdword_of_E (w_H W) mem' m' e (x + LPIS.s10_end str)).
        -- lia.
        -- destruct CE as ((_ & BYE') & _). cbn [BC.cells_bytes BC.cbytes] in BYE'. rewrite app_nil_r in BYE'.
           exact BYE'.
        -- intros k Hk. apply HE'. cbv beta. left. lia.
      * rewrite (ts_errno B TB).
        apply (rd32_of_E (w_H W) mem' m' TFIB_ERRNO (LPIS.s10_errno str (Z_to_bv 64 ev))).
        -- destruct CR as ((_ & BYR) & _). cbn [BC.cells_bytes BC.cbytes] in BYR. rewrite app_nil_r in BYR.
           exact BYR.
        -- intros k Hk. apply HE'. cbv beta. right. unfold aerrno_cell. rewrite (ts_errno B TB). lia.
Qed.

End s.
