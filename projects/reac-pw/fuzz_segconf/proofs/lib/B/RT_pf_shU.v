(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 702 of its 749 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/pj_write.v, with its module paths and module names changed; 496 of its 536 lines of code are new or changed and 709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/ReaderKB.v, with its module paths and module names changed; 211 of its 235 lines of code are new or changed and 512 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FMrt_lift.v, with its module paths and module names changed; 345 of its 399 lines of code are new or changed and 181 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_shU.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 3 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file); names: TfibSyms -> SegBSyms. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* ASan's printf_common at fuzz_manifest.asan in the shared contracts' form: sh_apcommon_realizesUz (FMsnprintfSx.v)
   for printf_common's family RT_pf_sh.FF_pcom, from the relocated Bz walk (RT_pf_bz.v pcom_call). The grammar part
   and the family are RT_pf_sh.v; Param lifts this contract to the chain's family and constants (FMsnprintfSx.v
   sh_apcommon_realizesUz_weaken).
   Pre side: the walk runs on the cleaned store (FMbz_clean.v); its premises come from the contract's
   - fmt_at / pf_args_asan (the format's and the %s strings' bytes, their range check: FMbz_str chk_ok_of_view and
     chkr_of_view here), words_at (the argument slots), the stack window (RtBzBridge.stk_of_apresent),
   - ARU (the runtime's cells: RtBzPre.m2s_of_ARm over the allocator's memory, which agrees with the real one below
     the shadow, RtPFupoison.ARU_mem_low), consts_view over every read-only byte (PCM_CR; RtBzClean.rom_eq).
   Post side: the walk changes only [sp - PCOM_DEPTH, sp) inside the contract's window [sp - K, sp); ARU is kept by
   RtPFupoison.ARU_frame, as RtBzLift.rt_post_roU_win keeps it. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFH RtBzLift.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2y YFl3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtBzStr RtBzBridge RtBzClean RtBzPre.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require RT_pf_Tbl RT_pf_bz RT_pf_sh.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.F_achk.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcbits.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcrr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pchead.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxgram.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxlist.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.K.I_vprintfw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Module BzMS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.MState.
Module BzE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Module BzC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Module BzSh := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Module BzR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Module BzK := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_consts.
Module BzQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Module BzD := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.D_kit.
Module BzA := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.F_achk.
Module BzP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pck.
Module BzB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcbits.
Module BzRR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcrr.
Module BzH := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pchead.
Module BzG := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxgram.
Module BzX := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxlist.
Module BzV := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.K.I_vprintfw.
Module LMS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.
Module R6 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Module CL := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzClean.
Module BZS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzStr.
Module PRE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzPre.
Module RTB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_bz.
Module RTT := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_Tbl.
Module RTS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_sh.

(* every read-only byte of fm's image: the non-writable segments *)
Definition PCM_CR : list (Z * Z) :=
  map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (List.filter (fun s => negb (seg_writable s)) tfibsegs).

Lemma pcm_cr_rom : forall a, in_rom tfibsegs a -> Exists (in_zr a) PCM_CR.
Proof.
  intros a (sg & Hin & Hw & Hr). apply Exists_exists.
  exists (Z.of_N (seg_base sg), Z.of_N (seg_size sg)). split; [|unfold in_zr; cbn [fst snd]; lia].
  unfold PCM_CR. apply in_map_iff. exists sg. split; [reflexivity|]. apply List.filter_In. split; [exact Hin | rewrite Hw; reflexivity].
Qed.

(* ---- the grammar's arguments ---- *)
Lemma ck_args_fm : forall m lo q ps args T ws,
  pf_text ps args = Some T -> Forall RTS.pf_fm_pc ps -> (length args <= length ws)%nat ->
  (forall i w s, nth_error ws i = Some w -> nth_error args i = Some (APtr s) ->
     BzX.ck_arg m lo q (Z_to_bv 64 w) (BzG.PA_s s) None) ->
  BzX.ck_args m lo q (map (Z_to_bv 64) ws) (map RTS.pa_of args) (RTS.pc_cin ps).
Proof.
  intros m lo q ps. induction ps as [|p ps IH]; intros args T ws HT HK HL HS.
  - cbn in HT. destruct args; [destruct ws; simpl; exact I | discriminate HT].
  - inversion HK as [|? ? Hp HK']; subst. destruct p; try destruct Hp.
    + cbn [pf_text] in HT. destruct (pf_text ps args) as [T'|] eqn:HT'; [|discriminate HT].
      exact (IH args T' ws HT' HK' HL HS).
    + cbn [pf_text] in HT. destruct args as [|[v|u|s] args']; try discriminate HT.
      destruct (pf_text ps args') as [T'|] eqn:HT'; [|discriminate HT].
      destruct ws as [|w ws']; [cbn in HL; lia|].
      simpl. split.
      * exact (HS 0%nat w s eq_refl eq_refl).
      * apply (IH args' T' ws' HT' HK' ltac:(cbn in HL; lia)).
        intros i w' s' E1 E2. exact (HS (S i) w' s' E1 E2).
    + cbn [pf_text] in HT. destruct args as [|[k|u|s0] [|[v|u'|s] args']]; try discriminate HT.
      destruct ((0 <=? k) && (k <=? Z.of_nat (length s))); [|discriminate HT].
      destruct (pf_text ps args') as [T'|] eqn:HT'; [|discriminate HT].
      destruct ws as [|w1 [|w2 ws']]; [cbn in HL; lia | cbn in HL; lia|].
      simpl. split; [exact I|]. split; [exact I|].
      apply (IH args' T' ws' HT' HK' ltac:(cbn in HL; lia)).
      intros i w' s' E1 E2. exact (HS (S (S i)) w' s' E1 E2).
Qed.

Lemma pf_fm_pc_of : forall ps, Forall pf_fm_piece ps -> Forall RTS.pf_fm_pc ps.
Proof. intros ps H. eapply Forall_impl; [|exact H]. intros p Hp. destruct p; exact Hp. Qed.

Lemma pf_text_len : forall ps args T, pf_text ps args = Some T -> Forall RTS.pf_fm_pc ps ->
  forall rd rs ws, pf_args_asan rd rs ws args -> (length args <= length ws)%nat.
Proof.
  intros ps args T _ _ rd rs. induction args as [|a args IH]; intros ws H; [cbn; lia|].
  destruct ws as [|w ws]; [destruct H|]. destruct H as [_ H]. cbn. specialize (IH ws H). lia.
Qed.

(* the same two facts for any pieces: ck_arg asks nothing of a scalar, nor of a string at a Some coverage entry *)
Lemma ck_args_any : forall m lo q args ws covs, (length args <= length ws)%nat ->
  (forall i w s, nth_error ws i = Some w -> nth_error args i = Some (APtr s) ->
     BzX.ck_arg m lo q (Z_to_bv 64 w) (BzG.PA_s s) None) ->
  BzX.ck_args m lo q (map (Z_to_bv 64) ws) (map RTS.pa_of args) covs.
Proof.
  intros m lo q args. induction args as [|a args IH]; intros ws covs HL HS; [destruct ws; exact I|].
  destruct ws as [|w ws]; [cbn in HL; lia|]. cbn [map BzX.ck_args]. split.
  - destruct a as [v|u|s]; cbn [RTS.pa_of BzX.ck_arg]; [exact I | exact I|].
    destruct (BzG.vhd_cov covs); [exact I | exact (HS 0%nat w s eq_refl eq_refl)].
  - apply IH; [cbn in HL; lia|]. intros i w' s' E1 E2. exact (HS (S i) w' s' E1 E2).
Qed.

Lemma args_asan_len : forall rd rs ws args, pf_args_asan rd rs ws args -> (length args <= length ws)%nat.
Proof.
  intros rd rs ws args. revert ws. induction args as [|a args IH]; intros ws H; [cbn; lia|].
  destruct ws as [|w ws]; [destruct H|]. destruct H as [_ H]. cbn. specialize (IH ws H). lia.
Qed.

(* the pf argument at index i and its slot word *)
Lemma args_asan_nth : forall rd rs ws args i w a,
  pf_args_asan rd rs ws args -> nth_error ws i = Some w -> nth_error args i = Some a -> pf_arg_asan rd rs w a.
Proof.
  intros rd rs ws args. revert ws. induction args as [|a0 args IH]; intros ws i w a H Hw Ha; [destruct i; discriminate Ha|].
  destruct ws as [|w0 ws]; [destruct H|]. destruct H as [H0 H1].
  destruct i as [|i]; cbn in Hw, Ha.
  - injection Hw as <-. injection Ha as <-. exact H0.
  - exact (IH ws i w a H1 Hw Ha).
Qed.

Lemma args_amem_nth : forall ws args i w s,
  RTS.pf_args_amem ws args -> nth_error ws i = Some w -> nth_error args i = Some (APtr s) ->
  amem_range w (Z.of_nat (length s) + 8).
Proof.
  intros ws args. revert ws. induction args as [|a0 args IH]; intros ws i w s H Hw Ha; [destruct i; discriminate Ha|].
  destruct ws as [|w0 ws]; [destruct i; discriminate Hw|].
  destruct i as [|i]; cbn in Hw, Ha.
  - injection Hw as <-. injection Ha as ->. destruct H as [H _]. exact H.
  - assert (H' : RTS.pf_args_amem ws args) by (destruct a0; [exact H | exact H | exact (proj2 H)]).
    exact (IH ws i w s H' Hw Ha).
Qed.

(* the first cell of a cell list *)
Lemma ro_cells_hd : forall m A c cs, BzS.ro_cells BzI.asegs m A (c :: cs) -> BzS.ro_cells BzI.asegs m A [c].
Proof.
  intros m A c cs (Hwf & Hb). change (c :: cs) with ([c] ++ cs) in Hwf, Hb.
  apply BzC.cells_wf_app in Hwf as [Hwf _]. rewrite BzC.cells_bytes_app in Hb.
  apply BzM.bytes_at_app in Hb as [Hb _]. split; [exact Hwf | exact Hb].
Qed.

(* ---- a range check over the real store's view, for the range-check walk's chkr ---- *)
Lemma chkr_of_view : forall (H : word -> bool) (mem : word -> option byte) p n,
  0 <= p -> 0 < n -> p + n < 2 ^ 63 -> n <= 2 ^ 40 -> BzK.region_in_mem p n ->
  range_addressable (BZS.aview_of H mem) BZS.FM_SHADOW_OFF p n ->
  BZS.hull_vis_of (BZS.aview_of H mem) p n ->
  BzA.chkr (mrestrict H mem) p n.
Proof.
  intros H mem p n Hp Hn Hpn Hn40 Hreg HRA HV.
  split; [apply BZS.acc_of_range_addressable; [lia | lia | lia | exact HRA]|].
  split; [|split; [exact Hreg | exact Hn40]].
  intros i Hi.
  assert (Hsp : 0 <= BzSh.shad p < 2 ^ 64) by (apply BZS.shad_range; lia).
  assert (Hsi : 0 <= BzSh.shad (p + i) < 2 ^ 64) by (apply BZS.shad_range; lia).
  assert (Hse : 0 <= BzSh.shad (p + n - 1) < 2 ^ 64) by (apply BZS.shad_range; lia).
  assert (Hm1 : BzSh.shad p <= BzSh.shad (p + i)).
  { unfold BzSh.shad. assert (p / 8 <= (p + i) / 8) by (apply Z.div_le_mono; lia). lia. }
  assert (Hm2 : BzSh.shad (p + i) <= BzSh.shad (p + n - 1)).
  { unfold BzSh.shad. assert ((p + i) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia). lia. }
  set (a := BzQ.al8 (BzSh.shad (p + i))).
  assert (Ha : BzQ.al8 (BzSh.shad p) <= a /\ a + 8 <= BzQ.al8 (BzSh.shad (p + n - 1)) + 8).
  { unfold a, BzQ.al8. split; [apply Z.mul_le_mono_nonneg_l; [lia | apply Z.div_le_mono; lia]|].
    assert (8 * (BzSh.shad (p + i) / 8) <= 8 * (BzSh.shad (p + n - 1) / 8))
      by (apply Z.mul_le_mono_nonneg_l; [lia | apply Z.div_le_mono; lia]). lia. }
  assert (Hal : 0 <= BzQ.al8 (BzSh.shad p) /\ BzQ.al8 (BzSh.shad (p + n - 1)) + 8 <= 2 ^ 64)
    by (unfold BzQ.al8; Z.div_mod_to_equations; lia).
  exists (BZS.word_of_mem (mrestrict H mem) a).
  apply BZS.ro_C8_of_vis; [lia | lia |].
  intros j Hj.
  assert (HN : BZS.aview_of H mem (a + j) <> None).
  { apply HV. unfold BZS.FM_SHADOW_OFF. unfold a, BzQ.al8, BzSh.shad, BzSh.SHB in *.
    Z.div_mod_to_equations. lia. }
  destruct (BZS.aview_of H mem (a + j)) as [v|] eqn:E; [|exfalso; apply HN; reflexivity].
  exists (Z_to_bv 8 v). apply BZS.bytes_at1_of_view; [lia | exact E].
Qed.

(* the range check reads only shadow bytes, all below 2^47 *)
Lemma chkr_clean : forall m p n, CL.rom_eq m -> 0 <= p -> p + n <= 2 ^ 47 ->
  BzA.chkr m p n -> BzA.chkr (CL.clean m) p n.
Proof.
  intros m p n HE Hp Hn (HA & HW & HR). split; [|split; [|exact HR]].
  - intros i Hi. destruct (HA i Hi) as (b & Hb & Hs). exists b. split; [|exact Hs].
    apply (CL.bytes_at_clean m _ [b] HE); [|exact Hb]. unfold BzSh.shad, BzSh.SHB, BzM.UTOP. cbn [length].
    assert (0 <= (p + i) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
  - intros i Hi. destruct (HW i Hi) as (w & Hw). exists w.
    apply (CL.ro_cells_clean m _ _ HE); [|exact Hw].
    change (BzC.cells_size [BzC.C8 w]) with 8%nat. unfold BzQ.al8, BzSh.shad, BzSh.SHB, BzM.UTOP.
    assert (0 <= (p + i) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (0 <= 8 * (((p + i) / 8 + 2147450880) / 8) <= (p + i) / 8 + 2147450880)
      by (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | apply Z.mul_div_le; lia]).
    lia.
Qed.

(* bytes the real store's view reads are bytes of the walks' store *)
Lemma bytes_of_view : forall (H : word -> bool) mem p (l : list Z),
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs H mem (p + i) = Some (nth (Z.to_nat i) l 0)) ->
  BzM.bytes_at BzI.asegs (mrestrict H mem) p (map (Z_to_bv 8) l).
Proof.
  intros H mem p l Hp Hl HV. apply PRE.bytes_of_garr8; [exact Hp | exact Hl|].
  intros j Hj. pose proof (HV (Z.of_nat j) ltac:(lia)) as E. rewrite Nat2Z.id in E.
  split; [exact (YE2y.val_mem1_of_aview H mem _ _ E) | exact (YFl3.aview_range H mem _ _ E)].
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

(* ---- the read-only image as the image ---- *)
Lemma pcm_rom_eq : forall (W : world tfibsegs) mem, consts_view tfibsegs W mem PCM_CR -> CL.rom_eq (mrestrict (w_H W) mem).
Proof.
  intros W mem HCV. apply (CL.rom_eq_of_views B W mem TB).
  - intros a Hrom _ _. exact (HCV a (pcm_cr_rom a Hrom)).
  - intros a Hrom _. exact (HCV a (pcm_cr_rom a Hrom)).
Qed.

(* ---- the runtime's cells printf_common reads ---- *)
Local Ltac rwc RE H :=
  apply (CL.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BzM.UTOP; lia | vm_compute; reflexivity | exact H].
Local Ltac roc RE H :=
  apply (CL.ro_cells_clean _ _ _ RE); [cbn; unfold BzM.UTOP; lia | exact H].

Lemma pctx_of_ARU : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> CL.rom_eq (mrestrict (w_H W) mem) ->
  BzH.pctx (CL.clean (mrestrict (w_H W) mem)).
Proof.
  intros ly S U W mem md HARU RE.
  pose proof (PRE.m2s_of_ARm B TB ly S (w_H W) (unpoison U mem) (ARU_ARm tfibsegs B ly S U W mem md HARU)) as M.
  assert (AG : forall A n, 0 <= A -> A + n <= SHADOW_OFF ->
            BzD.agree_on (fun x => A <= x < A + n) (mrestrict (w_H W) (unpoison U mem)) (mrestrict (w_H W) mem)).
  { intros A n HA Hn a Ha. unfold mrestrict. destruct (w_H W a); [reflexivity|].
    symmetry. apply (ARU_mem_low tfibsegs B ly S U W mem md a HARU). unfold SHADOW_OFF in *. lia. }
  destruct M as (C1 & C2 & C3).
  pose proof (BzD.rw_cells_agree_nw BzI.asegs _ _ _ _ C1 (AG 0xa3210 32 ltac:(lia) ltac:(unfold SHADOW_OFF; lia))) as C1'.
  pose proof (BzD.rw_cells_agree_nw BzI.asegs _ _ _ _ C2 (AG 0xac7b8 8 ltac:(lia) ltac:(unfold SHADOW_OFF; lia))) as C2'.
  pose proof (BzD.rw_cells_agree_nw BzI.asegs _ _ _ _ C3 (AG 0xad4a0 24 ltac:(lia) ltac:(unfold SHADOW_OFF; lia))) as C3'.
  split.
  - split; [|split]; [rwc RE C1' | rwc RE C2' | rwc RE C3'].
  - unfold BzRR.pcells. split.
    + roc RE (ro_cells_hd _ _ _ _ (proj1 C1')).
    + roc RE (proj1 C2').
Qed.
(* ---- the post: the walk changed only [sp - PCOM_DEPTH, sp) of the cleaned store ---- *)
Definition pcm_shpost (K : Z) ly S (U : list (Z * Z)) (W : world tfibsegs) regs mem md : world tfibsegs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\
  same_but_materialized md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

Lemma pcm_post : forall (K : Z) ly S (U : list (Z * Z)) (W : world tfibsegs) regs mem md msc ms' model',
  ecall_preU tfibsegs B ly S U W regs mem md -> 2320 <= K -> ly_stk_lo ly + K <= spZ regs ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
  hclean CL.Dc msc -> R6.ms_eqv (unrestrict CL.Dc (mrestrict (w_H W) mem) msc) ms' -> same_but_materialized md model' ->
  ms_pc_val msc = LMS.ret_pc (getr regs 1) -> ms_fregs msc = fp_regs -> ms_svc_pending msc = None ->
  ms_resv msc = None -> ms_fcsr msc = fp_csr -> ms_rom msc = seg_rom tfibsegs ->
  (forall r, acallee_saved r -> getr (ms_regs msc) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall x : word, ~ (spZ regs - 2320 <= bv_unsigned x < spZ regs) -> ms_mem msc x = CL.clean (mrestrict (w_H W) mem) x) ->
  (forall a, spZ regs - 2320 <= a < spZ regs -> ms_mem msc (Z_to_bv 64 a) <> None) ->
  pcm_shpost K ly S U W regs mem md W (mkCfg (unrestrict (w_H W) mem ms') model').
Proof.
  intros K ly S U W regs mem md msc ms' model' HPRE HK Hslo HpresS Hcl Heqv Hsbm P0 F0 S0 R0 C0 RO0 KEEP MOUT MIN.
  destruct (CL.clean_window (mrestrict (w_H W) mem) msc (spZ regs - 2320) (spZ regs) Hcl MOUT MIN) as (MO & MN).
  set (ms0 := unrestrict CL.Dc (mrestrict (w_H W) mem) msc) in *.
  destruct HPRE as ((HAR & Hra & _ & _ & Hshi & _ & _ & _) & HOK & HPO).
  pose proof Heqv as (_ & _ & _ & _ & _ & _ & Emem & _). rewrite Emem in MO, MN.
  destruct (win_mem (w_H W) mem (ms_mem ms') (spZ regs - 2320) (spZ regs) MO MN
              ltac:(intros a Ha; apply HpresS; lia)) as (AV & VIS & HB & PRS).
  destruct (same_but_materialized_frame md model' Hsbm)
    as (_ & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E3).
  assert (HARU' : ARU tfibsegs B ly S U W (munrestrict (w_H W) mem (ms_mem ms')) model').
  { apply (ARU_frame tfibsegs B LAWS ly S U W mem md _ model' (conj HAR (conj HOK HPO)));
      [| exact VIS | exact E1 | exact E2 | exact E3 |].
    - intros a Hr Hown. apply AV; [exact Hr|]. intros Hw.
      exact (al_stack _ _ LAWS ly S W (unpoison U mem) md a HAR ltac:(lia) Hown).
    - intros a _ Hh. exact (HB a Hh). }
  split; [reflexivity|].
  exists (ms_regs ms'), (munrestrict (w_H W) mem (ms_mem ms')), model'.
  split; [unfold cfg_at; f_equal; exact (unrestrict_ret regs (w_H W) mem ms0 ms' Heqv Hra P0 F0 S0 R0 C0 RO0)|].
  split; [exact HARU'|].
  split; [intros r Hr; rewrite (ms_eqv_getr ms0 ms' _ Heqv); exact (KEEP r Hr)|].
  split; [exact Hsbm|].
  split; [intros a Ha Hn; apply AV; [exact Ha | lia] | exact PRS].
Qed.

(* ---- the contract ---- *)
(* for any piece predicate PK whose pieces have their pcx arm (RT_pf_sh.v pcom_pcx_arm; fm's non-%s printf widening) *)
Section PcomKU.
Variable PK : pf_piece -> Prop.
Hypothesis ARM_pcx : forall p, PK p -> RTS.pcom_pcx_arm p.

Theorem pcom_shzK : forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B (RTS.FF_pcomK PK) K PCM_CR RTT.PF_PRINTF_COMMON.
Proof.
  intros K HK ly S U W regs mem md f ap ws T HPRE Hlo HWIN R11 R12 HCV _ _ HWS HZD HAP0 HAP47 HFF.
  destruct HFF as (fmt & ps & args & HFA & HNE & HIMG & HP & HKP & HAA & HAM & HT & _).
  pose proof HPRE as ((HAR & Hra & H16 & _ & HSH & _ & _ & _) & HOK & HPO).
  assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
  pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as (LB & LH).
  pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR))) as LC.
  pose proof ASAN_CEIL_range as ((LC1 & _) & _). unfold ASAN_CEIL in LC, LC1.
  lazymatch type of LB with ?k <= _ => let v := eval vm_compute in k in change k with v in LB end.
  lazymatch type of LH with _ <= ?k => let v := eval vm_compute in k in change k with v in LH end.
  set (sp := spZ regs) in *. set (H := w_H W) in *.
  set (m0 := mrestrict H mem). set (m := CL.clean m0).
  pose proof (pcm_rom_eq W mem HCV) as RE. fold H m0 in RE.
  destruct HFA as (Hf0 & HFB & HFD & HFAM & HFRA & HFHV).
  destruct (RTS.pcomx_K PK ARM_pcx fmt ps args T HP HKP HT) as (OK & COV).
  pose proof (RTS.pf_parse_bytes fmt ps HP) as FB.
  assert (L1 : (1 <= length fmt)%nat) by (destruct fmt; [exfalso; exact (HNE eq_refl) | cbn; lia]).
  set (n := Z.of_nat (length fmt) + 1).
  assert (Hn : Z.of_nat (length (fmt ++ [0])) = n) by (unfold n; rewrite length_app; cbn [length]; lia).
  unfold TFIB_IMG_END in HIMG.
  (* the format *)
  assert (BYf : BzM.bytes_at BzI.asegs m f (BzB.zb8 (fmt ++ [0]))).
  { apply (CL.bytes_at_clean m0 f _ RE); [unfold BzB.zb8; rewrite length_map, Hn; unfold BzM.UTOP; lia|].
    apply (bytes_of_view H mem f (fmt ++ [0])); [lia | rewrite Hn; lia|].
    intros i Hi. rewrite Hn in Hi. apply HFB. unfold n in Hi. lia. }
  assert (CHK : BzQ.chk_ok m f n).
  { apply (CL.chk_ok_clean m0 f n RE); [lia | unfold n; lia|].
    apply BZS.chk_ok_of_view; [lia | unfold n; lia | unfold n; lia | unfold n; lia | | exact HFRA |].
    - unfold BzK.region_in_mem, BzR.kLowMemEnd. left. unfold n. lia.
    - apply BZS.hull_of_shadow_hull_vis. exact HFHV. }
  (* the stack *)
  assert (ST : BzF.stk BzI.asegs m (sp - K) sp).
  { apply (CL.stk_clean m0 (sp - K) sp); [unfold YF0x.TFIB_IMG_END; lia | unfold BzM.UTOP; lia|].
    apply RtBzBridge.stk_of_apresent; [lia | lia | exact HWIN]. }
  (* the slots *)
  assert (VS : forall i w a, nth_error (map (Z_to_bv 64) ws) i = Some w -> nth_error (map RTS.pa_of args) i = Some a ->
               BzX.sarg a ->
               BzS.ro_cells BzI.asegs m (ap + 8 * Z.of_nat i) [BzC.C8 w]
               /\ (ap + 8 * Z.of_nat i + 8 <= sp - 2320 \/ sp <= ap + 8 * Z.of_nat i)).
  { intros i w a Ew _ _. rewrite nth_error_map in Ew.
    destruct (nth_error ws i) as [wz|] eqn:Ez; [|discriminate Ew]. cbn in Ew. injection Ew as <-.
    assert (Hi : (i < length ws)%nat) by (apply nth_error_Some; rewrite Ez; discriminate).
    pose proof (HWS i Hi) as Hrw. rewrite (nth_error_nth ws i 0 Ez) in Hrw.
    pose proof (YFl3.rdword_range H mem _ _ Hrw) as Hwr.
    pose proof (YE2y.val_mem_of_rdword H mem _ _ Hrw) as VM.
    unfold zdisjoint in HZD. cbn [fst snd] in HZD.
    split.
    - apply (CL.ro_cells_clean m0 _ _ RE); [change (BzC.cells_size [BzC.C8 (Z_to_bv 64 wz)]) with 8%nat; unfold BzM.UTOP; lia|].
      apply (PRE.c8_of_val_mem m0 _ wz); [lia | lia | exact Hwr | exact VM].
    - lia. }
  (* the strings *)
  assert (STR : forall i w s, nth_error ws i = Some w -> nth_error args i = Some (APtr s) ->
                BzX.ck_arg m (sp - 2320) sp (Z_to_bv 64 w) (BzG.PA_s s) None).
  { intros i w s Ew Ea.
    pose proof (args_asan_nth _ _ ws args i w (APtr s) HAA Ew Ea) as (FS & Hw0 & Hlen & HB & _ & HD & _ & HRA & HHV).
    pose proof (args_amem_nth ws args i w s HAM Ew Ea) as HAMs.
    unfold amem_range, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in HAMs.
    set (l := Z.of_nat (length s)) in *.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply wz; lia).
    unfold BzX.ck_arg. rewrite Ew64. exists (map (Z_to_bv 8) s).
    rewrite length_map. fold l.
    split; [|split; [exact Hw0|split; [|split]]].
    - split.
      + replace (map (Z_to_bv 8) s ++ [BzSh.z8]) with (map (Z_to_bv 8) (s ++ [0])) by (rewrite map_app; reflexivity).
        apply (CL.bytes_at_clean m0 w _ RE); [rewrite length_map, length_app; cbn [length]; unfold BzM.UTOP; fold l; lia|].
        apply (bytes_of_view H mem w (s ++ [0])); [lia | rewrite length_app; cbn [length]; fold l; lia|].
        intros i0 Hi0. rewrite length_app in Hi0. cbn [length] in Hi0. apply HB. fold l in Hi0. lia.
      + intros Hin. apply in_map_iff in Hin as (c & Ec & Hc).
        pose proof (proj1 (Forall_forall _ _) FS c Hc) as Rc. cbv beta in Rc.
        apply (f_equal (@bv_unsigned 8)) in Ec. unfold BzSh.z8 in Ec.
        rewrite (PRE.u8z c) in Ec by lia. rewrite (PRE.u8z 0) in Ec by lia. lia.
    - rewrite Forall_forall in HD. specialize (HD _ (or_introl eq_refl)). unfold zdisjoint, str_end in HD. cbn [fst snd] in HD.
      fold l in HD. pose proof (Z.mod_pos_bound (w + l) 8 ltac:(lia)). lia.
    - lia.
    - apply (chkr_clean m0 w (l + 1) RE); [lia | lia|].
      apply chkr_of_view; [lia | lia | lia | lia | | exact HRA | apply BZS.hull_of_shadow_hull_vis; exact HHV].
      unfold BzK.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd. lia. }
  assert (CKA : BzX.ck_args m (sp - 2320) sp (map (Z_to_bv 64) ws) (map RTS.pa_of args)
                  (BzG.pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map RTS.pa_of args) (RTS.pc_cinK ps))).
  { rewrite COV. apply (ck_args_any m _ _ args ws _ (args_asan_len _ _ ws args HAA) STR). }
  (* the run *)
  eapply (CL.srr_of_clean_bz_eq W RTT.PF_PRINTF_COMMON regs mem md _ _ RE).
  - apply PRE.bz_canon.
    apply (RTB.pcom_call f ap (sp - K)).
    + exact R11.
    + exact R12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with sp. lia.
    + lazymatch goal with |- ?k + 8 <= _ => let v := eval vm_compute in k in change k with v end. lia.
    + change (bv_unsigned (reg_get regs 2)) with sp. lia.
    + exact H16.
    + change (bv_unsigned (reg_get regs 2)) with sp.
      exists fmt, (map RTS.pa_of args), (RTS.pc_cinK ps), (map (Z_to_bv 64) ws).
      split; [exact OK|]. split; [exact FB|]. split; [exact L1|]. split; [exact BYf|].
      split; [lia|]. split; [lia|]. split; [exact VS|]. split; [exact HAP0|].
      split; [rewrite length_map; lia|]. split; [exact CKA|]. split; [exact CHK|].
      exact (pctx_of_ARU ly S U W mem md HARU RE).
    + exact (CL.mem_inv_clean m0).
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    unfold BzV.pcom_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & _ & _ & ST').
    change (bv_unsigned (reg_get regs 2)) with sp in MU, ST'.
    destruct (PRE.bz_window m m' sp 2320 (sp - K) MU ST' ltac:(lia) ltac:(unfold YF0x.TFIB_IMG_END; lia)) as (MO & MN).
    apply (pcm_post K ly S U W regs mem md _ ms' model' HPRE HK Hlo HWIN Hcl Heqv Hsbm);
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | keep_regs | exact MO | exact MN].
Qed.
End PcomKU.

(* fm's pieces *)
Theorem pcom_shz : forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B RTS.FF_pcom K PCM_CR RTT.PF_PRINTF_COMMON.
Proof. intros K HK. exact (pcom_shzK RTS.pf_fm_pc RTS.pf_fm_pcx_arms K HK). Qed.

End s.
