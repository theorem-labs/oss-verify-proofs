(* The atoi entry's runtime contract, RtNumber.aatoi_realizes at 0x45230 (the trampoline `j 0x4d158`), from the
   committed walk lib/B/Bz/A/I_atoiw.v iatoi_spec, which starts at 0x45230 itself. Its two statement arguments are
   discharged by R_isPoisoned.rip_proof and lib/B/Prog/strtol_wrap_sb.v sb_proof (musl's strtol body, with
   fv = s10_val, fe = s10_end, fr = s10_errno of lib/B/Prog/__intscan_c.v, the same text as the contract's
   lib/Prog/__intscan_c.v).
   - pre side: the adapter (RtBzAdapt) and the cleaned-store layer (RtBzClean, RtBzPre) give the walk's bytes,
     range check, stack, store and the runtime's fixed cells; the flag byte 0xae438 + 29 = 0xae455 is the
     contract's own premise, the stack-protector pair 0xa6bf8 -> 0x604158 is its aguard_ok;
   - errno: the walk states it as the cell at tp - 164; ecall_pre pins tp to as_tp B = TFIB_TP = 0x5e4118, and
     0x5e4118 - 164 = 0x5e4074 = TFIB_ERRNO = as_errno B (A/YF0m.v:13,18);
   - post side: RtBzAdaptP.art_post_clean with E = aerrno_cell B; the errno cell lies in a segment of the image,
     so it is not hidden (w_Hoff), not read-only (RtBzClean.errno_not_ro) and not owned (al_owned_image and one
     computation over Tfib_owned_static). *)
(* The image-B twin of lib/A/Rt/RtLAtoi.v, for fuzz_command.asan-ubsan (no function proved): the B kit's
   walk (lib/B/Bz) and body proof (lib/B/Prog), B's contract (lib/B/Rt/RtNumber.v), the B bridge and adapter, and
   every A address replaced by its B twin (each re-read from image B); the proof text is the A file's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtBzHBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.__intscan_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strtol_wrap_sb.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Spec.CType.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_atoiw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strtolw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strtolfix.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.__intscan_c.
Module AIS := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.__intscan_c.
Module ACT := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Spec.CType.
Module SBP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.strtol_wrap_sb.
Module IA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_atoiw.
Module ISW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strtolw.
Module SFX := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.I_strtolfix.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Bz.A.R_isPoisoned.

(* ---- the walk's answer in the contract's words ---- *)

(* the walk's musl spec (lib/A/Prog) and the contract's (lib/Prog) are the same text *)
Lemma s10_val_eq : forall s, AIS.s10_val s = PIS.s10_val s.
Proof. intros s. reflexivity. Qed.

Lemma ndig_le : forall l, (AIS.ndig l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [AIS.ndig length]; [lia|]. destruct (ACT.c_digit b); lia. Qed.

Lemma skip_le : forall l, (length (ACT.skip_space l) <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [ACT.skip_space length]; [lia|]. destruct (ACT.c_space b); cbn [length]; lia. Qed.

Lemma rest_le : forall wd, (length (AIS.s10_rest wd) <= length wd)%nat.
Proof.
  intros wd. unfold AIS.s10_rest. pose proof (skip_le wd) as H.
  destruct (ACT.skip_space wd) as [|b r]; cbn [AIS.sign_split]; [cbn [snd length]; lia|].
  cbn [length] in H. destruct (bv_unsigned b =? 45); [cbn [snd]; lia|].
  destruct (bv_unsigned b =? 43); cbn [snd length]; lia.
Qed.

Lemma end_le : forall wd, 0 <= AIS.s10_end wd <= Z.of_nat (length wd).
Proof.
  intros wd. pose proof (rest_le wd) as R. pose proof (ndig_le (AIS.s10_rest wd)) as N.
  unfold AIS.s10_end, AIS.s10_nd. destruct (Nat.eqb (AIS.ndig (AIS.s10_rest wd)) 0); lia.
Qed.

(* the walk returns sx32 of strtol's word; the contract states bv_swrap 32 of its value *)
Lemma sx32_val : forall v, BM.sx32 (Z_to_bv 64 v) = w64 (bv_swrap 32 v).
Proof.
  intros v. unfold BM.sx32, w64. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (bv_modulus 64) with 18446744073709551616. f_equal.
  rewrite (Z.mod_eq v 18446744073709551616) by lia.
  replace (v - 18446744073709551616 * (v / 18446744073709551616) + 2147483648)
    with (v + 2147483648 + - (4294967296 * (v / 18446744073709551616)) * 4294967296) by lia.
  apply Z_mod_plus_full.
Qed.

(* byte k < 4 of a word, as le4 holds it and as rd32 reads it *)
Lemma le_byte4_shiftr : forall z k, (k < 4)%nat -> Z.shiftr z (8 * Z.of_nat k) mod 256 = YG0f.le_byte z 4 k.
Proof.
  intros z k Hk. unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32. change 256 with (2 ^ 8).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 8) as [L|L].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma le_byte4_mod64 : forall z k, (k < 4)%nat ->
  Z.shiftr (z mod 2 ^ 64) (8 * Z.of_nat k) mod 256 = YG0f.le_byte z 4 k.
Proof.
  intros z k Hk. unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32. change 256 with (2 ^ 8).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z_lt_le_dec n 8) as [L|L].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* ---- the errno cell of this image (computed) ---- *)

(* each of its four bytes lies in a segment of the image *)
Lemma errno_seg : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> exists sg, find_segment tfibsegs a 1 = Some sg.
Proof.
  intros a Ha.
  assert (C : forallb (fun k => match find_segment tfibsegs (TFIB_ERRNO + k) 1 with Some _ => true | None => false end)
                [0; 1; 2; 3] = true) by (vm_compute; reflexivity).
  assert (Hk : In (a - TFIB_ERRNO) [0; 1; 2; 3]) by (cbn; lia).
  pose proof (proj1 (forallb_forall _ _) C _ Hk) as X. cbv beta in X.
  replace (TFIB_ERRNO + (a - TFIB_ERRNO)) with a in X by lia.
  destruct (find_segment tfibsegs a 1) as [sg|]; [exists sg; reflexivity | discriminate X].
Qed.

Lemma errno_in_img : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. destruct (errno_seg a Ha) as (sg & Hsg).
  destruct (YK04.find_segment_some_spec tfibsegs a 1 sg Hsg) as (Hin & Hlo & Hhi).
  exists sg. split; [exact Hin | lia].
Qed.

(* no static owned range of the record meets it *)
Lemma errno_unowned_static : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha HE.
  assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst r))
                Tfib_owned_static = true) by (vm_compute; reflexivity).
  apply Exists_exists in HE as (r & Hr & Hz).
  pose proof (proj1 (forallb_forall _ _) C r Hr) as X. cbv beta in X.
  unfold in_zr in Hz. apply orb_true_iff in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Theorem cmd_atoi : RtNumber.aatoi_realizes tfibsegs B 0x45230 0xae455 0xa6bf8 0x604158.
Proof.
  unfold RtNumber.aatoi_realizes.
  intros ly S W regs mem md x str ev HFLAG HGUARD HPRE G10 Hx0 HSTR HRD HAM HTAIL HERR HSEPE HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & _ & _ & _ & _ & _ & Htp).
  pose proof HRD as (_ & _ & Hn32 & _).
  assert (HL : astr_len str = Z.of_nat (length str)) by reflexivity.
  assert (E4 : ESTACK = 4096) by reflexivity.
  assert (HXE : x + Z.of_nat (length str) + 8 <= 2 ^ 47).
  { pose proof HAM as H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. }
  (* the thread pointer and errno *)
  assert (EE : as_errno B = TFIB_ERRNO) by exact (ts_errno B TB).
  assert (EEn : as_errno B = 0x5e4074) by (rewrite EE; reflexivity).
  assert (ETP : bv_unsigned (reg_get regs 4) = TFIB_TP).
  { refine (eq_trans (f_equal bv_unsigned Htp) _). rewrite (ts_tp B TB). apply RtBzPre.u64z. unfold TFIB_TP. lia. }
  assert (ETPn : bv_unsigned (reg_get regs 4) = 0x5e4118) by (rewrite ETP; reflexivity).
  assert (ETE : TFIB_TP + -164 = TFIB_ERRNO) by (unfold TFIB_TP, TFIB_ERRNO; lia).
  assert (ESP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 x) by exact G10.
  (* the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.romN_of_rt B W mem HROM) as HRN.
  pose proof (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR)) as HRO.
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (RtBzClean.mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (RtBzPre.m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  (* the stack *)
  destruct (RtBzAdapt.stk_of_stk_pre B (3 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (LOB : 0x7fff7f800000 <= spZ regs - 3 * ESTACK) by lia.
  assert (ST : BF.stk BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) (spZ regs - 3 * ESTACK) (spZ regs)).
  { apply (RtBzClean.stk_clean (mrestrict (w_H W) mem) (spZ regs - 3 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* the string *)
  assert (BYm : BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x (str ++ [Z_to_bv 8 0])).
  { first [apply (RtBzAdapt.bz_str_bytes B) | apply RtBzAdapt.bz_str_bytes]; [exact HSTR | lia | lia]. }
  assert (BY : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) x (str ++ [Z_to_bv 8 0])).
  { apply (RtBzClean.bytes_at_clean _ x _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYm]. }
  (* the range check over every prefix the walk checks *)
  assert (CHK : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 ->
            BQ.chk_ok (RtBzClean.clean (mrestrict (w_H W) mem)) x nn).
  { intros nn Hnn. apply (RtBzClean.chk_ok_clean _ x nn RE); [lia | lia |].
    first [apply (RtBzAdapt.chk_of_read B (3 * ESTACK) W regs mem x (astr_len str + 1) nn (astr_len str))
          | apply (RtBzAdapt.chk_of_read (3 * ESTACK) W regs mem x (astr_len str + 1) nn (astr_len str))];
      [exact HRD | exact HAM | lia | lia | lia]. }
  assert (SEP0 : x + (astr_len str + 1) <= spZ regs - 3 * ESTACK \/ spZ regs <= x).
  { first [apply (RtBzAdapt.sep_of_read B (3 * ESTACK) W regs mem x (astr_len str + 1))
          | apply (RtBzAdapt.sep_of_read (3 * ESTACK) W regs mem x (astr_len str + 1))];
      [lia | lia | exact HRD]. }
  (* the stack-protector pair *)
  assert (GB : BM.bytes_at BI.asegs (mrestrict (w_H W) mem) 0xa6bf8 (BM.le8 (Z_to_bv 64 0x604158)) /\
               exists can, BM.bytes_at BI.asegs (mrestrict (w_H W) mem) 0x604158 (BM.le8 can)).
  { first [apply (RtBzAdapt.bz_guard_bytes B W mem 0xa6bf8 0x604158)
          | apply (RtBzAdapt.bz_guard_bytes W mem 0xa6bf8 0x604158)]; [exact HGUARD | lia | lia | lia | lia]. }
  destruct GB as (GOTm & can & CANm).
  assert (GOT : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) ISW.STRTOL_SSP_GOT
                  (BM.le8 (Z_to_bv 64 ISW.STRTOL_SSP_GUARD))).
  { apply (RtBzClean.bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold ISW.STRTOL_SSP_GOT, BM.UTOP; lia | exact GOTm]. }
  assert (CAN : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) ISW.STRTOL_SSP_GUARD (BM.le8 can)).
  { apply (RtBzClean.bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold ISW.STRTOL_SSP_GUARD, BM.UTOP; lia | exact CANm]. }
  (* the runtime's fixed cells: const cells of the record (A/YF0m.v), on the cleaned store *)
  assert (RO8 : forall a v, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
            0 <= a -> a + 8 <= 2 ^ 47 -> 0 <= v < 2 ^ 64 ->
            BS.ro_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) a [BC.C8 (Z_to_bv 64 v)]).
  { intros a v E Ha Hb Hv. apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia |].
    exact (RtBzPre.ro_c8 B TB ly S (w_H W) mem a v (proj1 HAR) E Ha ltac:(lia) Hv). }
  assert (RO1 : forall a v, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
            0 <= a -> a + 1 <= 2 ^ 47 -> 0 <= v < 256 ->
            BS.ro_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) a [BC.C1 (Z_to_bv 8 v)]).
  { intros a v E Ha Hb Hv. apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia |].
    exact (RtBzPre.ro_c1 B TB ly S (w_H W) mem a v (proj1 HAR) E Ha ltac:(lia) Hv). }
  assert (ICX : SFX.icells_sx (RtBzClean.clean (mrestrict (w_H W) mem))).
  { split.
    - exact (RO8 0xa5f40 0x142768 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (RO1 0x14285d 0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (RSLOT : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) 0xa7de8 (BM.le8 (BM.wa ISW.STRTOL))).
  { pose proof (RO8 0xa7de8 0x9e4e0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as C.
    destruct C as (_ & Hb). cbn [BC.cells_bytes BC.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (AFSLOT : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) 0xa5f48 (BM.le8 (BM.wa 0xae438))).
  { pose proof (RO8 0xa5f48 0xae438 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as C.
    destruct C as (_ & Hb). cbn [BC.cells_bytes BC.cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  (* asan_inited, a writable byte *)
  assert (AI : BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) 0xb1918 [BC.C1 (Z_to_bv 8 1)]).
  { apply (RtBzClean.rw_cells_clean _ _ _ RE); [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity |].
    apply RtBzPre.rw_of_ro; [| vm_compute; reflexivity].
    exact (RtBzPre.ro_c1 B TB ly S (w_H W) mem 0xb1918 1 (proj1 HAR) ltac:(vm_compute; reflexivity)
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* the replace_str flag byte: the contract's premise *)
  assert (AF29 : BM.bytes_at BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) (0xae438 + 29) [Z_to_bv 8 1]).
  { change (0xae438 + 29) with 0xae455.
    apply (RtBzClean.bytes_at_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia |].
    first [apply (RtBzAdapt.bz_bytes_of_abytes B) | apply RtBzAdapt.bz_bytes_of_abytes]; [| lia | cbn; lia].
    intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i. exact HFLAG. }
  (* the errno cell, at tp - 164 *)
  assert (ERRm : BS.ro_cells BI.asegs (mrestrict (w_H W) mem) TFIB_ERRNO [BC.C4 (Z_to_bv 64 ev)]).
  { unfold BS.ro_cells, BC.cells_at. split; [cbn; tauto|]. cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
    split; [unfold TFIB_ERRNO; lia|]. split; [rewrite BM.length_le4; unfold TFIB_ERRNO; lia|].
    intros i Hi. rewrite BM.length_le4 in Hi.
    rewrite EE in HERR. pose proof (HERR i Hi) as Hb.
    unfold aview in Hb. rewrite <- RtBzPre.mrd_mbyte in Hb.
    destruct (BM.mrd BI.asegs (mrestrict (w_H W) mem) (BM.wa (TFIB_ERRNO + Z.of_nat i))) as [b|] eqn:Eb;
      [|discriminate Hb].
    cbn [option_map] in Hb. injection Hb as Hb.
    unfold BM.le4. rewrite (RtBzPre.nth_le_bytes 4 _ i Hi). f_equal. apply bv_eq.
    rewrite Hb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
    symmetry. apply le_byte4_mod64. exact Hi. }
  assert (ERR : BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict (w_H W) mem)) (bv_unsigned (reg_get regs 4) + -164)
                  [BC.C4 (Z_to_bv 64 ev)]).
  { rewrite ETP, ETE.
    apply (RtBzClean.rw_cells_clean _ _ _ RE);
      [unfold TFIB_ERRNO; lia | cbn; unfold BM.UTOP, TFIB_ERRNO; lia
      | change (BC.cells_size [BC.C4 (Z_to_bv 64 ev)]) with 4%nat; vm_compute; reflexivity |].
    apply RtBzPre.rw_of_ro; [exact ERRm |].
    change (BC.cells_size [BC.C4 (Z_to_bv 64 ev)]) with 4%nat. vm_compute. reflexivity. }
  (* the walk's arithmetic premises *)
  pose proof (end_le str) as FE.
  assert (A47 : x + Z.of_nat (length str) + 1 <= 2 ^ 47) by lia.
  assert (N40 : Z.of_nat (length str) + 1 <= 2 ^ 40) by lia.
  assert (LO : spZ regs - 3 * ESTACK + IA.IATOI_DEPTH <= bv_unsigned (reg_get regs 2))
    by (unfold IA.IATOI_DEPTH; lia).
  assert (LOLO : BR.kHighShadowEnd < spZ regs - 3 * ESTACK) by (unfold BR.kHighShadowEnd; lia).
  assert (SPH : bv_unsigned (reg_get regs 2) <= 2 ^ 47) by lia.
  assert (A0 : 0 <= x) by lia.
  assert (SEPS : x + Z.of_nat (length str) + 1 <= spZ regs - 3 * ESTACK \/ bv_unsigned (reg_get regs 2) <= x)
    by lia.
  clear SEP0.
  assert (SEPT : bv_unsigned (reg_get regs 4) + -164 + 4 <= spZ regs - 3 * ESTACK \/
                 bv_unsigned (reg_get regs 2) <= bv_unsigned (reg_get regs 4) + -164) by (left; lia).
  assert (SEPG : ISW.STRTOL_SSP_GOT + 8 <= spZ regs - 3 * ESTACK \/ bv_unsigned (reg_get regs 2) <= ISW.STRTOL_SSP_GOT)
    by (left; unfold ISW.STRTOL_SSP_GOT; lia).
  assert (SEPGU : ISW.STRTOL_SSP_GUARD + 8 <= spZ regs - 3 * ESTACK \/
                  bv_unsigned (reg_get regs 2) <= ISW.STRTOL_SSP_GUARD)
    by (left; unfold ISW.STRTOL_SSP_GUARD; lia).
  assert (SEPGT : ISW.STRTOL_SSP_GUARD + 8 <= bv_unsigned (reg_get regs 4) + -164 \/
                  bv_unsigned (reg_get regs 4) + -164 + 4 <= ISW.STRTOL_SSP_GUARD)
    by (right; unfold ISW.STRTOL_SSP_GUARD; lia).
  assert (SEPTA : bv_unsigned (reg_get regs 4) + -164 + 4 <= x \/
                  x + Z.of_nat (length str) + 1 <= bv_unsigned (reg_get regs 4) + -164) by lia.
  clear HSEPE.
  assert (TPSH : bv_unsigned (reg_get regs 4) + -164 + 4 <= 0x7fff8000 \/
                 0x10007fff8000 <= bv_unsigned (reg_get regs 4) + -164) by (left; lia).
  assert (TPMETA : bv_unsigned (reg_get regs 4) + -164 + 4 <= 0xa5f40 \/
                   0x14285e <= bv_unsigned (reg_get regs 4) + -164) by (right; lia).
  (* the run *)
  pose proof (IA.iatoi_spec (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
    (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 11) (reg_get regs 12)
    (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
    (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
    (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
    (reg_get regs 31) fp_regs fp_csr (RtBzClean.clean (mrestrict (w_H W) mem)) x str _ _ _ (Z_to_bv 64 ev) can
    (spZ regs - 3 * ESTACK) RIP.rip_proof SBP.sb_proof BY A47 N40 ERR GOT CAN ST LO LOLO SPH A0 CHK
    SEPS SEPT SEPG SEPGU SEPGT SEPTA M2S ICX AI MI RSLOT AFSLOT AF29 FE TPSH TPMETA) as RUN.
  clear SEPS SEPT SEPG SEPGU SEPGT SEPTA TPSH TPMETA.
  rewrite <- R10 in RUN.
  refine (RtBzClean.bz_run_clean B TB W 0x45230 regs mem md _ _ HRN HRO
            (RtBzAdaptP.evt_grows _ _ (RtBzPre.bz_canon _ regs 0x45230 _ RUN)) _).
  intros msc ms' model' HQG Hcl Heqv Hsbm _.
  destruct HQG as (HQ & GROW).
  unfold IA.iatoi_post in HQ.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI' & ST' & ERRC).
  assert (EM : ms_mem msc = m') by (rewrite Emsc; reflexivity).
  refine (RtBzAdaptP.art_post_clean B LAWS (3 * ESTACK) 2640 ly S W regs mem md (aerrno_cell B) _ msc ms' model'
            HPRE _ Hcl Heqv Hsbm _ _ _ _ _ _ _ _ _ _ _ _).
  - lia.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. reflexivity.
  - rewrite Emsc. keep_regs.
  - (* outside the window and errno the walk kept the store *)
    intros y Hy1 Hy2. rewrite EM. apply MU. cbn [BF.outside].
    unfold aerrno_cell in Hy2. unfold IA.IATOI_DEPTH.
    split; [lia | split; [lia | exact I]].
  - (* every byte of the window is in the store *)
    intros a Ha. rewrite EM.
    exact (proj2 (RtBzPre.bz_window m' m' (spZ regs) 2640 (spZ regs - 3 * ESTACK)
             (BF.munch_refl [(spZ regs - 2640, spZ regs)] m') ST' ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)) a Ha).
  - exact GROW.
  - (* the errno cell: unowned, a byte of the store, not dropped, not hidden *)
    intros a Ha. unfold aerrno_cell in Ha. rewrite EE in Ha.
    assert (EA : bv_unsigned (Z_to_bv 64 a) = a) by (apply RtBzPre.u64z; unfold TFIB_ERRNO in Ha; lia).
    destruct (errno_seg a Ha) as (sg & Hsg).
    split; [| split; [unfold TFIB_ERRNO in Ha; lia | split]].
    + intros HO. apply (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR (errno_in_img a Ha))) in HO.
      rewrite (ts_owned B TB) in HO. exact (errno_unowned_static a Ha HO).
    + apply RtBzClean.Dc_false.
      * apply RtBzClean.errno_not_ro. rewrite EA. exact Ha.
      * rewrite EA. unfold BM.UTOP, TFIB_ERRNO in *. lia.
    + destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [|reflexivity]. exfalso.
      pose proof (w_Hoff W (Z_to_bv 64 a) EH) as X. rewrite EA, Hsg in X. discriminate X.
  - (* the answer *)
    intros regs' mem' HR _ HV. cbv beta. split.
    + rewrite HR. rewrite Emsc.
      transitivity (BM.sx32 (Z_to_bv 64 (AIS.s10_val str))); [reflexivity|].
      rewrite sx32_val, s10_val_eq. reflexivity.
    + intros k Hk.
      rewrite (HV (as_errno B + Z.of_nat k)) by (unfold aerrno_cell; lia).
      rewrite EM, EE.
      destruct ERRC as ((_ & EB) & _). destruct EB as (_ & _ & EB).
      cbn [BC.cells_bytes BC.cbytes] in EB. rewrite app_nil_r in EB. rewrite ETP, ETE in EB.
      rewrite (EB k ltac:(rewrite BM.length_le4; exact Hk)).
      unfold BM.le4. rewrite (RtBzPre.nth_le_bytes 4 _ k Hk). cbn [option_map]. f_equal.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      rewrite (le_byte4_shiftr _ k Hk). reflexivity.
Qed.

End s.
