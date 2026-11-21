(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require SBase.

Module S_MatchL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_MLOOP : Z := 93144.
Definition L_MAFTER : Z := 93168.
Definition L_SETLEN : Z := 93184.

End FXG.
Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

End FXG.
Ltac prog_transfer P :=
  first [ exact P
        | let P1 := fresh in let P2 := fresh in let P3 := fresh in
          dand P as (P1 & P2 & P3); unfold PROG; icx_cbn; split; [exact P1 | split; [exact P2 |]];
          first [ exact P3
                | let E := fresh in let C := fresh in
                  destruct P3 as [E | [E C]];
                  first [ left; exact E
                        | right; split; [exact E | clear - C; modes_cbv; lia_std]
                        | exfalso; clear - C; modes_cbv; lia_std ] ] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma sinv_bad_of : forall cx st lf cf, sinv cx st lf cf -> sinv cx (bad_of st) lf cf.
Proof.
  intros cx st lf cf (R & W & P & Mo). destruct cx, st. unfold sinv, bad_of in *. icx_cbn.
  split; [exact R | split; [exact W | split; [unfold PROG in P; icx_cbn; prog_transfer P |]]].
  dand Mo as (Mr & Mf & Mrest). unfold MODE in *. icx_cbn.
  split; [unfold reach; cbv [HEAD DICTID MEM BAD]; right; lia_std |].
  split; [intros Hf; destruct (Mf Hf) as [_ Hc]; split; [right; reflexivity | exact Hc] |].
  clear. split_conj; mode_vacuous.
Qed.
Lemma meas_bad_of : forall cx st, meas cx (bad_of st) + rank (t_mode st) = meas cx st.
Proof. intros cx st. destruct cx, st. unfold meas, Wm, bad_of. icx_cbn. change (rank BAD) with 0. lia_std. Qed.

Lemma mem_u32_u8 : forall M a v, mem_u32 R_segs M a v -> mem_u8 R_segs M a v.
Proof.
  intros M a v H. unfold mem_u32, mem_u8, mem_is in *.
  pose proof (mem_is_firstn R_segs M a (Z_to_le_bytes 4 v) 1 H ltac:(cbn; lia_std)) as H1.
  cbn [firstn Z_to_le_bytes] in H1. exact H1.
Qed.


Lemma zfupd_byte : forall (f : Z -> Z) i v lo hi,
  (forall j, lo <= j < hi -> 0 <= f j < 256) -> 0 <= v < 256 -> forall j, lo <= j < hi -> 0 <= zfupd f i v j < 256.
Proof. intros f i v lo hi Hf Hv j Hj. unfold zfupd. destruct (Z.eqb_spec j i); [lia_std | apply Hf; lia_std]. Qed.

End FXG.
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' R_segs _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

End FXG.
Ltac tstore_arrP fd Ha i HP HPres :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          (let HP' := fresh in pose proof (HPres M a v HP ltac:(zlia) ltac:(zlia)) as HP'; clear HP; rename HP' into HP);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia]
                    | idtac "tstore_arrP: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma mloop_w : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz w wn si c m : Z) (fo fw : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = w + si -> zget_l Rb l kS3 = ob + c -> zget_l Rb l kA4 = w + si + m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= si -> si + m <= wn -> 0 <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 -> 0 < w -> w + wn <= 140737488355328 -> ZSEP (w + wn <= ob \/ ob + osz <= w) ->
  mem_wr R_segs M ob osz -> mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_arr 1 R_segs M w wn fw -> (forall i, 0 <= i < wn -> 0 <= fw i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA3 = w + si + m -> zget R' kS3 = ob + c + m ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kRA = zget_l Rb l kRA -> zget R' kT6 = zget_l Rb l kT6 -> zget R' kT4 = zget_l Rb l kT4 ->
     zget R' kS9 = zget_l Rb l kS9 -> zget R' kS4 = zget_l Rb l kS4 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS8 = zget_l Rb l kS8 ->
     zget R' kS11 = zget_l Rb l kS11 -> zget R' kA2 = zget_l Rb l kA2 ->
     mem_wr R_segs M' ob osz -> mem_arr 1 R_segs M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     mem_arr 1 R_segs M' w wn fw -> P M' ->
     realizes R_segs (zcfg R_segs L_MAFTER (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_MLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz w wn si c m fo fw Hh La3 Ls3 La4 Hm1 Hm2 Hsi1 Hsi2 Hc1 Hc2
    Hob1 Hob2 Hw1 Hw2 Swob Wob HOB Rfo Hwin Rfw HP HPres K; [lia|].
  zkeys. unfold L_MLOOP, L_MAFTER in *. pose proof two64_eq as TW64.
  pose proof (Rfw si ltac:(lia)) as Rb0.
  tld1 Hwin si Rfw.
  zstep Rfd.
  tstore_arrP Rfd HOB c HP HPres.
  zstep Rfd.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fw si) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw si))) end;
      try zreg; try assumption.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz w wn (si + 1) (c + 1) (m - 1) (zfupd fo c (fw si)) fw Hh) end;
      try zreg; try assumption; try lia.
    intros R' M' fo' Ma3 Ms3 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob' HOB' Rfo' Hwin' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    all: cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; assumption.
Qed.

Lemma mloop_o : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz s c m : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = ob + s -> zget_l Rb l kS3 = ob + c -> zget_l Rb l kA4 = ob + s + m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= s -> s <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 ->
  mem_wr R_segs M ob osz -> mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA3 = ob + s + m -> zget R' kS3 = ob + c + m ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kRA = zget_l Rb l kRA -> zget R' kT6 = zget_l Rb l kT6 -> zget R' kT4 = zget_l Rb l kT4 ->
     zget R' kS9 = zget_l Rb l kS9 -> zget R' kS4 = zget_l Rb l kS4 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS8 = zget_l Rb l kS8 ->
     zget R' kS11 = zget_l Rb l kS11 -> zget R' kA2 = zget_l Rb l kA2 ->
     mem_wr R_segs M' ob osz -> mem_arr 1 R_segs M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     P M' ->
     realizes R_segs (zcfg R_segs L_MAFTER (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_MLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz s c m fo Hh La3 Ls3 La4 Hm1 Hm2 Hs1 Hs2 Hc2
    Hob1 Hob2 Wob HOB Rfo HP HPres K; [lia|].
  zkeys. unfold L_MLOOP, L_MAFTER in *. pose proof two64_eq as TW64.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  tld1 HOB s Rfo.
  zstep Rfd.
  tstore_arrP Rfd HOB c HP HPres.
  zstep Rfd.
  zstep Rfd.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fo s))) end;
      try zreg; try assumption.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz (s + 1) (c + 1) (m - 1) (zfupd fo c (fo s)) Hh) end;
      try zreg; try assumption; try lia.
    intros R' M' fo' Ma3 Ms3 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob' HOB' Rfo' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    all: cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; assumption.
Qed.

Definition st_upd (st : ist) (m copy len' : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st + copy) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len' (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_upd : forall cx st lf cf m copy len',
  sinv cx st lf cf -> (t_mode st = MATCH \/ t_mode st = LIT) ->
  1 <= copy -> copy <= c_osz cx - t_cout st -> 0 <= len' -> len' <= t_length st ->
  ((m = MATCH /\ t_mode st = MATCH /\ 1 <= len') \/ m = LEN) ->
  sinv cx (st_upd st m copy len') lf cf /\ meas cx (st_upd st m copy len') < meas cx st.
Proof.
  intros cx st lf cf m copy len' (R & W & P & Mo) Hmode Hc1 Hc3 Hl1 Hl2 Hm.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_upd, meas, Wm in *. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  assert (Mr : reach mode) by mode_get Mo.
  assert (Mf : flags = -1 -> (mode = HEAD \/ mode = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP mode -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mma : mode = MATCH -> 1 <= length /\ length < 65536 /\ offset < 98304) by mode_get Mo.
  clear Mo.
  assert (Hfl : flags <> -1) by (intros E; destruct (Mf E) as [HM _]; clear - HM Hmode; cbv [MATCH LIT HEAD BAD] in *; lia_std).
  assert (TL : tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf)
    by (apply Mlive; clear - Hmode; unfold codes_liveP; cbv [MATCH LIT LEN_] in *; lia_std).
  assert (HMA : m = MATCH -> 1 <= len' /\ len' < 65536 /\ offset < 98304)
    by (intros E; destruct Hm as [(_ & E2 & E3) | E'];
        [dand (Mma E2) as (A1 & A2 & A3); clear - A2 A3 E3 Hl2; lia_std | clear - E E'; cbv [MATCH LEN] in *; lia_std]).
  clear Mma.
  split; [split; [| split; [exact W | split]] |].
  - clear W P1 P2 Mr Mf Mlive TL HMA. unfold RNG. icx_cbn. split_conj; try assumption; try lia_std.
  - clear - P1 P2 P3 Hc1 Hmode Hm. unfold PROG, Wm. icx_cbn.
    split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct Hmode as [-> | ->]; destruct Hm as [(-> & _) | ->]; modes_cbv; lia_std ].
  - clear W P1 P2 P3. unfold MODE. icx_cbn.
    split; [clear - Hm; unfold reach; cbv [HEAD DICTID MEM MATCH LEN] in *; lia_std |].
    split; [intros E; exfalso; exact (Hfl E) |].
    split_conj; first [ intros _; exact TL | exact HMA
                      | destruct Hm as [(-> & _) | ->]; mode_vacuous ].
  - clear - Hm Hmode Hc1. assert (rank m <= 18) by (destruct Hm as [(-> & _)| ->]; [change (rank MATCH) with 14 | change (rank LEN) with 18]; lia_std).
    assert (13 <= rank mode) by (destruct Hmode as [-> | ->]; [change (rank MATCH) with 14 | change (rank LIT) with 13]; lia_std). lia_std.
Qed.

Definition PM (cx : ictx) (fin : Z -> Z) (M0 : mem) (md : Z) (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  s_std cx fin M /\ mem_u32 R_segs M (c_p cx + 8) md /\ st_rest R_segs cx st M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf /\ mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf /\
  mpostL R_segs M0 M (fp_loop cx).

Lemma PM_store : forall cx fin M0 md st lf cf M a v,
  ctx_ok ROMHI_S cx -> PM cx fin M0 md st lf cf M -> c_ob cx <= a -> a + 1 <= c_ob cx + c_osz cx ->
  PM cx fin M0 md st lf cf (wbytes M (w64 a) (Z_to_le_bytes 1 v)).
Proof.
  intros cx fin M0 md st lf cf M a v CX H Ha1 Ha2.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  dand H as (STD & Hm & SR & RET & OUT & HL & HC & HP0). open_std STD. unfold PM. icx_cbn. cbv [N_LENS N_CODES] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zmem_transport M a (Z_to_le_bytes 1 v).
  split_conj; try assumption; try close_std; try exact HAG.
Qed.

Lemma out_arr : forall M ob osz, mem_wr R_segs M ob osz -> 0 <= ob -> 0 <= osz -> ob + osz <= two64 ->
  exists fo, mem_arr 1 R_segs M ob osz fo /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).
Proof.
  intros M ob osz W H1 H2 H3. destruct (mem_wr_arr_exists_R M ob osz W H1 H2 H3) as [fo [A B]].
  exists fo. split; [exact A | intros i _; apply B].
Qed.
End FXG.
End S_MatchL.

Module S_Match.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_M4C : Z := 93108.
Definition L_M54 : Z := 93116.
Definition L_M30 : Z := 93080.
Definition L_M3C : Z := 93092.

Definition m_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout hold bits out dput : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kT6 = -16180 /\ zget R kT4 = 30 /\
  zget R kS9 = JTAB_ADDR /\ zget R kS4 = 16209 /\ zget R kS2 = n - cin /\ zget R kRA = osz - cout /\
  zget R kS7 = hold /\ zget R kS8 = bits /\ zget R kS11 = q + cin /\
  zget R kS3 = ob + cout + dput.
End FXG.
Ltac open_mregs H := unfold m_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS8 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kRA kS3 kS5 kS4 kS7 kS7 kS2 kS0 kS11 kS10 kT3 kT4 kS9 kT6 JTAB_ADDR] in H; destr_conj H.
Ltac close_mregs := unfold m_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS8 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kRA kS3 kS5 kS4 kS7 kS7 kS2 kS0 kS11 kS10 kT3 kT4 kS9 kT6 JTAB_ADDR]; split_conj;
                   first [zreg | match goal with |- ?G => idtac "close_mregs FAIL" G; fail end].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Theorem match_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = MATCH -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_MATCH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (PR3' : out = osz - cout0) by (destruct PR3 as [E | [_ C]]; [exact E | exfalso; clear - C; cbv [CHECK MATCH] in C; lia]).
  clear PR3. rename PR3' into PR3.
  assert (HMA : 1 <= length /\ length < 65536 /\ offset < 98304)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : MATCH = MATCH -> _ |- _ => exact (H eq_refl) end).
  dand HMA as (HL1 & HL16 & HO17). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_MATCH, L_M4C, L_M54, L_M30, L_M3C, L_MLOOP, L_MAFTER, L_SETLEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KD KD00 KRA1 KRL KB11 KBA3 KL KRT.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd true.
    unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd false. clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (_ & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  pose proof SOUT as S80. unfold s_out in S80. icx_cbn.
  unfold WIN in WIN_. icx_cbn. cbv [WIN_SIZE] in WIN_. destruct WIN_ as [WIN0 WIN1].
  assert (Hwh32 : whave <= 32768 /\ wnext <= 32768) by (destruct (Z.eq_dec w 0) as [E|E]; [destruct (WIN0 E) | destruct (WIN1 E)]; lia).
  assert (JA : forall R' M' (copy : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out copy R' -> zget R' kA2 = copy ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
       (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
               MATCH copy (length - copy)) lf cf M' ->
    realizes R_segs (zcfg R_segs 93168 (zupd R' []) M' MD) T).
  { intros R' M' copy MR G13 Hc1 Hc2 Hc3 HPM. open_mregs MR. cbv [kA2] in G13.
    dand HPM as (STD' & Hm' & SR' & RET' & OUT' & HL' & HC' & HP0'). unfold st_upd in SR', RET', OUT'. icx_cbn.
    pose proof SR' as SR2. unfold st_rest in SR2. icx_cbn. dand SR2 as (_ & _ & _ & _ & C92' & _).
    tstep1 Rfd.
    clear C92'.
    tstep1 Rfd.
    unfold KSETMODE, L_SETMODE in KSM. unfold KDISP10, L_DISP10 in KD10. zkeys.
    destruct (Z.eq_dec (length - copy) 0) as [E0 | N0].
    + zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf LEN copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ MATCH lf cf SI1 ME1) end.
      * unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
      * exact STD'.
      * exact Hm'.
      * exact SR'.
      * exact RET'.
      * exact OUT'.
      * exact HL'.
      * exact HC'.
      * exact HP0'.
    + zbr Rfd false.
      zstep Rfd.
      pose proof (sinv_upd _ _ lf cf MATCH copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia)
                    ltac:(left; split; [reflexivity | split; [reflexivity | lia]])) as [SI1 ME1].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD10 Rx Mx _ lf cf SI1 ME1) end.
      * unfold s_regs_d10, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      * unfold k_mem, st_at; icx_cbn. split_conj; try assumption. }
  assert (J54 : forall R2 (copy : Z) (src : Z + Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R2 ->
    zget R2 kA2 = copy -> zget R2 kA4 = length ->
    1 <= copy -> copy <= length -> copy <= osz - cout ->
    match src with
    | inl so => zget R2 kA3 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R2 kA3 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0
    end ->
    realizes R_segs (zcfg R_segs 93116 (zupd R2 []) M MD) T).
  { intros R2 copy src MR Q13 Q15 Hk1 Hk2 Hk3 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in Q13, Q15, HSRC.
    clear C60 C72 C7144 S72 S80.
    assert (Q14 : exists from, zget R2 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : match src with inl so => from = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => from = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (destruct src; rewrite <- Q14; exact HSRC).
    clear HSRC.
    tstep1 Rfd.
    clear C92 SREST.
    tstep1 Rfd.
    destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
    assert (HPM : PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
                     (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             MATCH copy (length - copy)) lf cf Mc)
      by (unfold PM, st_upd, s_ret, s_out, st_rest; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; exact HAG) end.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    destruct src as [so | si].
    - dand HS2 as (Hfrom & Hso1 & Hso2). subst from.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_o (Z.to_nat copy) Pm Rx lx Mx MD T ob osz so cout copy fo Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E14 E20 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob9 HOB9 Rfo9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia; [close_mregs | zreg].
    - dand HS2 as (Hfrom & Hsi1 & Hsi2 & Hw0). subst from.
      pose proof Ww as Ww32. rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in Ww32. cbv [WIN_SIZE] in Ww32.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (out_arr Mx w 32768 Ww32 ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fw & HWA & Rfw) end.
      pose proof (sep_w_ob ROMHI_S _ SEP) as SWO. icx_cbn. cbv [WIN_SIZE] in SWO.
      assert (SWO' : ZSEP (w + 32768 <= ob \/ ob + osz <= w)) by (unfold ZSEP; clear - SWO Hw0; lia). clear SWO.
      lazymatch type of HPM with ?Pm _ => lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_w (Z.to_nat copy) Pm Rx lx Mx MD T ob osz w 32768 si cout copy fo fw Hh) end end.
      all: try zreg. all: try lia. all: try assumption.
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 E14 E20 E3 E4 E5 E26 E11 E12 E2 E32 E30 E31 E22 E25 E19 E24 E9 E27 E13 Wob9 HOB9 Rfo9 Hwin9 HPM9.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia; [close_mregs | zreg]. }
  assert (J4C : forall R' (copy0 : Z) (src : Z + Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA4 = length ->
    1 <= copy0 -> copy0 <= length ->
    match src with
    | inl so => zget R' kA3 = ob + so /\ 0 <= so /\ so <= cout
    | inr si => zget R' kA3 = w + si /\ 0 <= si /\ si + copy0 <= 32768 /\ w <> 0
    end ->
    realizes R_segs (zcfg R_segs 93108 (zupd R' []) M MD) T).
  { intros R' copy0 src MR G13 G15 Hc1 Hc2 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in G13, G15, HSRC.
    assert (Q14 : exists from, zget R' 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : forall copy, copy <= copy0 -> match src with inl so => zget R' 14 = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => zget R' 14 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (intros copy Hcp; destruct src; [exact HSRC | dand HSRC as (X1 & X2 & X3 & X4); repeat split; try assumption; lia]).
    assert (G14 : zget R' 14 = from) by exact Q14.
    clear HSRC Q14.
    zstep Rfd || idtac.
    destruct (Z_lt_dec copy0 (osz - cout)) as [Hlt | Hge].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx copy0 src) end; try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 copy0 ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx (osz - cout) src) end; try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 (osz - cout) ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end. }
  clear J54.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zsetreg (cout - cout0) ltac:(rewrite ?swrap32_small by lia; lia).
  tstep1 Rfd.
  destruct (Z_lt_dec (cout - cout0) offset) as [Hwin | Hout].
  2: {
    zbr Rfd true.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx length (inl (cout - offset))) end; try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  zbr Rfd false.
  tstep1 Rfd.
  tstep1 Rfd.
  destruct (Z_lt_dec whave (offset - (cout - cout0))) as [Hfar | Hok].
  {
    zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    unfold KBADMSG_S10, L_BADMSG_S10 in KB10.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
    - apply sinv_bad_of. exact SI0.
    - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
      cbn [t_mode] in MB. change (rank MATCH) with 14 in MB. clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - cbv [kA2]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66236 by (symmetry; zreg) end. rewrite TW64. lia.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; try exact HAG. }
  zbr Rfd true.
  assert (Hw0 : w <> 0) by (intros E; destruct (WIN0 E); lia).
  dand (WIN1 Hw0) as (Wh1 & Wn1 & Whn). clear WIN0 WIN1.
  rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in C60. cbv [WIN_SIZE] in C60.
  assert (J3C : forall R' (copy0 si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA3 = si -> zget R' kA4 = length ->
    1 <= copy0 -> copy0 <= length -> 0 <= si -> si + copy0 <= 32768 ->
    realizes R_segs (zcfg R_segs 93092 (zupd R' []) M MD) T).
  { intros R' copy0 si MR G13 G14 G15 Hc1 Hc2 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3 kA4] in G13, G14, G15.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx copy0 (inr si)) end; try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  assert (J30 : forall R' (cp si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = cp -> zget R' kA3 = si ->
    1 <= cp -> cp < 98304 -> 0 <= si -> si + cp <= 32768 ->
    realizes R_segs (zcfg R_segs 93080 (zupd R' []) M MD) T).
  { intros R' cp si MR G13 G14 Hc1 Hc98 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3] in G13, G14.
    tstep1 Rfd.
    destruct (Z_lt_dec cp length) as [Hlt | Hge].
    - zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx cp si) end; try zreg; try lia; close_mregs.
    - zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx length si) end; try zreg; try lia; close_mregs. }
  clear J3C J4C.
  tstep1 Rfd.
  destruct (Z_lt_dec wnext (offset - (cout - cout0))) as [Hwrap | Hlin].
  - zbr Rfd false.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0) - wnext) (32768 - (offset - (cout - cout0) - wnext))) end; try zreg; try lia; close_mregs.
  - zbr Rfd true.
    tstep1 Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0)) (wnext - (offset - (cout - cout0)))) end; try zreg; try lia; close_mregs.
Qed.

Theorem lit_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LIT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LIT (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_ MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_LIT, L_SETLEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  open_K K. clear KD KD10 KD00 KRA1 KRL KB11 KB10 KBA3 KL KRT.
  destruct (Z.eq_dec (osz - cout) 0) as [Hleft0 | Hleft].
  { zbr Rfd false.
    zstep Rfd.
    unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end.
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  zbr Rfd true.
  clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (_ & _ & _ & _ & C92 & _).
  pose proof (mem_u32_u8 _ _ _ C92) as B92.
  destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
  zstep Rfd.
  clear B92 C92.
  tstep1 Rfd.
  tstore_arr Rfd HOB (cout).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  unfold KSETMODE, L_SETMODE in KSM. zkeys.
  pose proof (sinv_upd _ _ lf cf LEN 1 length SI0 ltac:(right; reflexivity) ltac:(lia) ltac:(cbn [c_osz t_cout]; lia) ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ LIT lf cf SI1 ME1) end.
  - unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
  - close_std.
  - exact Hmode.
  - unfold st_upd; icx_cbn. exact SREST.
  - exact SRET.
  - exact SOUT.
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_MATCH : arm_stmt L_MATCH MATCH.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply match_s; try eassumption.
Qed.

Theorem arm_LIT : arm_stmt L_LIT LIT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply lit_s; try eassumption.
Qed.
End FXG.
End S_Match.

Module S_DistL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_DLOOP1 : Z := 92452.
Definition L_D04 : Z := 92524.
Definition L_DLOOP2 : Z := 92612.
Definition L_D8BC : Z := 92708.
Definition L_DXLOOP : Z := 92824.
Definition L_DX80 : Z := 92900.
Definition L_LXLOOP : Z := 87140.
Definition L_LX60 : Z := 89320.
Definition L_LVX_L1 : Z := 93492.
Definition L_LVX_L2 : Z := 93576.
Definition L_LVX_EXT : Z := 93536.

Lemma pow2_pos : forall k, 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.
Lemma pow2_15 : forall k, 0 <= k <= 15 -> 1 <= 2 ^ k <= 32768.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 32768 with (2 ^ 15); apply pow2_le; lia]. Qed.
Lemma pow2_48 : forall k, 0 <= k <= 48 -> 1 <= 2 ^ k <= 281474976710656.
Proof. intros k Hk. split; [pose proof (pow2_pos k ltac:(lia)); lia | change 281474976710656 with (2 ^ 48); apply pow2_le; lia]. Qed.
Lemma pow2_add8 : forall k, 0 <= k -> 2 ^ (k + 8) = 256 * 2 ^ k.
Proof. intros. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. Qed.

Lemma mask_not_sllw : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl (-1) (k mod 32))) (-1) = 2 ^ k - 1.
Proof.
  intros k Hk. rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (B : 1 <= 2 ^ k <= 1073741824) by (split; [pose proof (pow2_pos k ltac:(lia)); lia | change 1073741824 with (2 ^ 30); apply pow2_le; lia]).
  rewrite swrap32_small by lia. rewrite lxor_m1. lia.
Qed.
Lemma land_mask_r : forall x k, 0 <= k -> 0 <= Z.land x (2 ^ k - 1) < 2 ^ k.
Proof. intros. apply land_ones_range. assumption. Qed.
Lemma land_mask_l : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k - 1) x < 2 ^ k.
Proof. intros. rewrite Z.land_comm. apply land_ones_range. assumption. Qed.
Lemma srl_hold : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= bits <= 63 -> 0 <= k <= 63 ->
  Z.shiftr (hold mod 18446744073709551616) (k mod 64) = hold / 2 ^ k.
Proof.
  intros hold bits k Hh Hb Hk.
  assert (2 ^ bits <= 2 ^ 63) by (apply pow2_le; lia).
  rewrite (Z.mod_small k 64) by lia. rewrite Z.mod_small by (change 18446744073709551616 with (2 * 2 ^ 63); lia).
  apply Z.shiftr_div_pow2. lia.
Qed.
Lemma hold_shr_bound : forall hold bits k, 0 <= hold < 2 ^ bits -> 0 <= k <= bits ->
  0 <= hold / 2 ^ k < 2 ^ (bits - k).
Proof.
  intros hold bits k Hh Hk. pose proof (pow2_pos k ltac:(lia)).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (bits - k)) with bits by lia. lia.
Qed.
Lemma srlw_small : forall x k, 0 <= x < 2147483648 -> 0 <= k <= 31 ->
  bv_swrap 32 (Z.shiftr (x mod 4294967296) (k mod 32)) = x / 2 ^ k.
Proof.
  intros x k Hx Hk. rewrite (Z.mod_small k 32) by lia. rewrite (Z.mod_small x 4294967296) by lia.
  rewrite Z.shiftr_div_pow2 by lia. pose proof (pow2_pos k ltac:(lia)).
  assert (0 <= x / 2 ^ k <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | nia]]).
  apply swrap32_small. lia.
Qed.
Lemma shl_byte : forall b s, 0 <= b < 256 -> 0 <= s <= 63 -> Z.shiftl b (s mod 64) = b * 2 ^ s.
Proof. intros b s Hb Hs. rewrite (Z.mod_small s 64) by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma hold_pull1 : forall hold bits b, 0 <= hold < 2 ^ bits -> 0 <= bits -> 0 <= b < 256 ->
  0 <= b * 2 ^ bits /\ 0 <= hold + b * 2 ^ bits < 2 ^ (bits + 8).
Proof.
  intros hold bits b Hh Hbits Hb. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (pow2_pos bits Hbits). nia.
Qed.
Lemma shiftl_2 : forall x, Z.shiftl x (2 mod 64) = 4 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (2 mod 64)) with 4. lia. Qed.
Lemma zext32_shift30 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) (30 mod 64) = 4 * x.
Proof.
  intros x Hx. change (30 mod 64) with 30. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma shiftl_1_pow : forall k, 0 <= k -> Z.shiftl 1 k = 2 ^ k.
Proof. intros. rewrite Z.shiftl_1_l. reflexivity. Qed.
Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as E. rewrite (Z.lxor_lor _ _ D), Z.lor_ldiff_and in E.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha). lia.
Qed.
Lemma land_range_r : forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof. intros a b Hb. split; [apply Z.land_nonneg; lia | rewrite Z.land_comm; apply land_le_l; lia]. Qed.

End FXG.
Ltac tld4_op Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_op R_segs _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_bits Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_bits R_segs _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_val Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_val R_segs _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' R_segs _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac zlastval := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?x) :: _)) _ _) _ => x end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Fixpoint keptc (Rb : tree Z) (l : list (positive * Z)) (R' : tree Z) (ks : list positive) : Prop :=
  match ks with
  | [] => True
  | k :: ks' => zget R' k = zget_l Rb l k /\ keptc Rb l R' ks'
  end.
Definition KS_D1 : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 16; 18; 19; 20; 21; 23; 25; 26; 28; 29; 30; 32]%positive.
Definition KS_D2 : list positive := [2; 3; 4; 5; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 23; 26; 27; 28]%positive.
Definition KS_X : list positive := [2; 3; 4; 5; 6; 7; 9; 10; 11; 12; 14; 19; 20; 21; 23; 25; 26; 27; 28; 29; 30; 32]%positive.

End FXG.
Ltac keptc_close := cbv [keptc KS_D1 KS_D2 KS_X]; split_conj; try exact I; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac keptc_chain HK := cbv [keptc KS_D1 KS_D2 KS_X] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma d_loop1 : forall (N : nat) Rb l M MD T (q n da nd db dm c0 b0 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA5 = da -> zget_l Rb l kA7 = dm -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kT1 = q + ci ->
  zget_l Rb l kT0 = B -> zget_l Rb l kA3 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kA4 = code_bits (rdD (Z.land dm H)) -> zget_l Rb l kA6 = da + 4 * Z.land dm H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdD (Z.land dm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  dm = 2 ^ db - 1 -> 1 <= db -> db <= 15 -> 2 ^ db <= nd -> tab_ok DISTS rdD db nd = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M da nd rdD ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_D1 ->
     realizes R_segs (zcfg R_segs L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA3 = B' -> zget R' kT0 = B' -> zget R' kS7 = H' ->
     zget R' kA4 = code_bits (rdD (Z.land dm H')) -> zget R' kA6 = da + 4 * Z.land dm H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdD (Z.land dm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D1 ->
     realizes R_segs (zcfg R_segs L_D04 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_DLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db dm c0 b0 ci B H fin rdD Hh La5 La7 La2 Lt1 Lt0 La3 Ls7 La4 La6 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP1, L_D04, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  pose proof (land_mask_l H db ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_l H' db ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land dm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Htab (Z.land dm H').
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (rdD (Z.land dm H')))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db dm c0 b0 (ci + 1) (B + 8) H' fin rdD Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.

Lemma d_loop2 : forall (N : nat) Rb l M MD T (q n da nd db lo v m2 c1 b1 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kT1 = m2 -> zget_l Rb l kA4 = db -> zget_l Rb l kA6 = v -> zget_l Rb l kA5 = da ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  zget_l Rb l kA7 = n - ci -> zget_l Rb l kT6 = q + ci -> zget_l Rb l kT4 = B -> zget_l Rb l kT0 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kT3 = da + 4 * (v + Z.land H m2 / 2 ^ db) -> zget_l Rb l kT2 = code_bits (rdD (v + Z.land H m2 / 2 ^ db)) ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (db + lo) - 1 -> 1 <= db -> db <= 15 -> 1 <= lo -> lo <= 15 - db -> 0 <= v -> v + 2 ^ lo <= nd -> nd <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdD (v + j))) = false /\ term_ok DISTS (15 - db) (rdD (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M da nd rdD ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_D2 ->
     realizes R_segs (zcfg R_segs L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kT5 = q + ci' -> zget R' kA7 = n - ci' -> zget R' kT0 = B' -> zget R' kT4 = B' -> zget R' kS7 = H' ->
     zget R' kT3 = da + 4 * (v + Z.land H' m2 / 2 ^ db) -> zget R' kT2 = code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D2 ->
     realizes R_segs (zcfg R_segs L_D8BC (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_DLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db lo v m2 c1 b1 ci B H fin rdD Hh Lt1 La4 La6 La5 La2 La3 Ls11
    La7 Lt6 Lt4 Lt0 Ls7 Lt3 Lt2 HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_DLOOP2, L_D8BC, L_LVX_L2 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (db + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_DISTS in TM0 as [Hbits0 _].
  assert (HB29 : B <= 29) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_r H' (db + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.
  zsetreg (Z.land H' m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_DISTS in TM1 as [Hbits1 _].
  zstep Rfd.
  zsetreg (v + Z.land H' m2 / 2 ^ db) ltac:(lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.
  tld4_bits Htab (v + Z.land H' m2 / 2 ^ db).
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdD Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G31 G18 G6 G30 G24 G29 G8 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.

Lemma x_loop : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n ext c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_LXLOOP /\ pcx = L_LX60) \/ (pc = L_DXLOOP /\ pcx = L_DX80)) ->
  m_halted MD = None ->
  zget_l Rb l kA3 = ext -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kA6 = q + ci -> zget_l Rb l kA4 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < ext -> ext <= 15 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_X ->
     realizes R_segs (zcfg R_segs L_LVX_EXT (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kA5 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA4 = B' -> zget R' kS7 = H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> ext <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_X ->
     realizes R_segs (zcfg R_segs pcx (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n ext c0 b0 ci B H fin Hpc Hh La3 La2 La6 La4 Ls7 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hext HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  zkeys. unfold L_LXLOOP, L_LX60, L_DXLOOP, L_DX80, L_LVX_EXT in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct Hpc as [[-> ->] | [-> ->]]; (
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ first [ zbr Rfd true | zbr Rfd false; zstep Rfd ];
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_close ]
    | first [ zbr Rfd false | zbr Rfd true ];
      pose proof (Rfin ci ltac:(lia)) as Rb1;
      tld1 Hin ci Rfin;
      tstep1 Rfd;
      zstep Rfd;
      zstep Rfd;
      zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia);
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      tstep1 Rfd;
      zstep Rfd;
      zsetreg (H + fin ci * 2 ^ B) ltac:(lia);
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      zstep Rfd;
      destruct (Z_lt_dec (B + 8) ext) as [Hmore | Hdone];
      [ zbr Rfd true;
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH _ _ Rx lx Mx MDx Tx q n ext c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end;
        [ first [left; split; reflexivity | right; split; reflexivity] | ..];
        try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chain HK
      | zbr Rfd false;
        zstep Rfd;
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end;
        try zreg; try lia; keptc_close ] ]).
Qed.



Definition tabsP (cx : ictx) (st : ist) (cf : Z -> Z) (M : mem) (na nd : Z) : Prop :=
  let la := cp_addr cx (t_lc st) in let da := cp_addr cx (t_dc st) in
  mem_arr 4 R_segs M la na (rdc cf (t_lc st)) /\ mem_arr 4 R_segs M da nd (rdc cf (t_dc st)) /\
  tab_ok LENS (rdc cf (t_lc st)) (t_lb st) na = true /\ tab_ok DISTS (rdc cf (t_dc st)) (t_db st) nd = true /\
  0 < la /\ la + 4 * na <= c_zc cx /\ 0 < da /\ da + 4 * nd <= c_zc cx /\ na <= 2048 /\ nd <= 2048 /\
  la mod 2 = 0 /\ da mod 2 = 0 /\
  ZSEP (la + 4 * na <= c_ob cx \/ c_ob cx + c_osz cx <= la) /\ ZSEP (la + 4 * na <= c_p cx \/ c_p cx + 1384 <= la) /\
  ZSEP (da + 4 * nd <= c_ob cx \/ c_ob cx + c_osz cx <= da) /\ ZSEP (da + 4 * nd <= c_p cx \/ c_p cx + 1384 <= da) /\
  ZSEP (la + 4 * na <= c_p cx + 7160 \/ c_p cx + 7176 <= la) /\ ZSEP (da + 4 * nd <= c_p cx + 7160 \/ c_p cx + 7176 <= da) /\
  (65536 <= c_p cx -> 65536 <= la /\ 65536 <= da).

Lemma live_tabs : forall cx st lf cf M,
  ctx_ok ROMHI_S cx -> RNG cx st lf cf -> tables_live cx st cf -> rom_ok M ->
  mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  exists na nd, tabsP cx st cf M na nd.
Proof.
  intros cx st lf cf M CX R TL ROM Hcodes.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  pose proof (sep_p_ob ROMHI_S _ SEP) as Spob. pose proof (sep_p_rom ROMHI_S _ SEP) as Sprom.
  icx_cbn. cbv [STATE_SIZE ROM_LO_ALL ROMHI_S] in Spob, Sprom.
  dand AL as (ALu & ALp & ALw). icx_cbn.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold RNG in R; icx_cbn; cbv [N_CODES N_LENS] in R; destr_conj R.
  unfold tables_live in TL. unfold tabsP. icx_cbn. cbv [N_CODES ] in *.
  destruct lc as [o1 | |]; destruct dc as [o2 | |]; try contradiction.
  -
    dand TL as (Ho1 & Hlb & Hdb & Ho2 & Ho2nx & Hnx & TOKL & TOKD). subst o1.
    exists o2, (nx - o2). unfold cp_addr, rdc. icx_cbn. cbv [o_codes].
    split_conj; try assumption; try (unfold ZSEP; lia).
    + replace (p + 1384 + 4 * 0) with (p + 1384 + 4 * 0) by lia.
      exact (mem_arr_sub R_segs 4 M (p + 1384) 1444 cf 0 o2 Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (mem_arr_sub R_segs 4 M (p + 1384) 1444 cf o2 (nx - o2) Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + clear - ALp. Z.to_euclidean_division_equations; lia.
    + clear - ALp Ho2. Z.to_euclidean_division_equations; lia.
  -
    destruct TL as [Hlb Hdb]. subst lb db.
    exists 512, 32. unfold cp_addr, rdc. cbv [LENFIX_ADDR DISTFIX_ADDR].
    split_conj; try exact lenfix_ok; try exact distfix_ok; try (unfold ZSEP; lia).
    + apply (mem_arr_ext R_segs 4 M 67422 512 lenfix_f). { exact (rom_lenfix_arr M ROM). } exact lenfix_f_model.
    + apply (mem_arr_ext R_segs 4 M 69470 32 distfix_f). { exact (rom_distfix_arr M ROM). } exact distfix_f_model.
    + reflexivity.
    + reflexivity.
Qed.

End FXG.
Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

End FXG.
Ltac prog_transfer P :=
  first [ exact P
        | let P1 := fresh in let P2 := fresh in let P3 := fresh in
          dand P as (P1 & P2 & P3); unfold PROG; icx_cbn; split; [exact P1 | split; [exact P2 |]];
          first [ exact P3
                | let E := fresh in let C := fresh in
                  destruct P3 as [E | [E C]];
                  first [ left; exact E
                        | right; split; [exact E | clear - C; modes_cbv; lia_std]
                        | exfalso; clear - C; modes_cbv; lia_std ] ] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition st_pull (st : ist) (ci H B : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) ci (t_cout st) H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma sinv_pull : forall cx st lf cf ci H B,
  sinv cx st lf cf ->
  t_cin st <= ci -> ci <= c_n cx -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  sinv cx (st_pull st ci H B) lf cf /\ meas cx (st_pull st ci H B) <= meas cx st.
Proof.
  intros cx st lf cf ci H B (R & W & P & Mo) H1 H2 H3 H4 H5 H6 H7 H8.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_pull, meas, Wm in *. icx_cbn.
  unfold RNG in R. icx_cbn. destr_conj R.
  unfold PROG, Wm in P. icx_cbn. dand P as (P1 & P2 & P3).
  split; [split; [| split; [exact W | split; [| exact Mo]]] |].
  - clear W Mo P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mo. unfold PROG, Wm. icx_cbn. clear - P1 P2 P3 H1 H8. lia_std.
  - clear - H8. lia_std.
Qed.

Definition st_dx (st : ist) (m off ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) off ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma sinv_to_distext : forall cx st lf cf off ex,
  sinv cx st lf cf -> t_mode st = DIST -> 0 <= off -> off < 65536 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_dx st DISTEXT off ex) lf cf /\ meas cx (st_dx st DISTEXT off ex) < meas cx st.
Proof.
  intros cx st lf cf off ex SI Hm Ho1 Ho2 He1 He2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_dx, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (DIST = HEAD \/ DIST = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP DIST -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST DIST last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mold : DIST = DIST -> 1 <= length /\ length < 65536) by mode_get Mo. specialize (Mold eq_refl).
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive Mold. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Mold Ho1 Ho2 He1 He2; destr_conj Mold; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_match : forall cx st lf cf off,
  sinv cx st lf cf -> t_mode st = DISTEXT -> 0 <= off -> off < 98304 ->
  sinv cx (st_dx st MATCH off (t_extra st)) lf cf /\ meas cx (st_dx st MATCH off (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf off SI Hm Ho1 Ho2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_dx, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (DISTEXT = HEAD \/ DISTEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP DISTEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST DISTEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  assert (Mold : DISTEXT = DISTEXT -> extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536) by mode_get Mo. specialize (Mold eq_refl).
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive Mold. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Mold Ho1 Ho2; destr_conj Mold; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma shiftl_3 : forall x, Z.shiftl x (3 mod 64) = 8 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ (3 mod 64)) with 8. lia. Qed.

Definition KS_L1 : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 14; 15; 16; 17; 18; 20; 21; 23; 24; 26; 27; 29; 30; 32]%positive.
End FXG.
Ltac keptc_closeL := cbv [keptc KS_L1]; split_conj; try exact I; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma stub_L1 : forall (pc : Z) Rb l M MD T (q n c0 b0 u rv : Z),
  (pc = L_LVX_L1 \/ pc = L_LVX_EXT) -> m_halted MD = None ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 -> zget_l Rb l kSP = u + -224 ->
  0 <= n - c0 -> n - c0 < 4294967296 -> mem_u64 R_segs M (u + -160) rv ->
  (forall R', zget R' kS8 = b0 + 8 * (n - c0) -> zget R' kS11 = q + n -> zget R' kS2 = 0 -> zget R' kS1 = rv ->
     keptc Rb l R' KS_L1 -> realizes R_segs (zcfg R_segs L_LEAVE (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs pc (zupd Rb l) M MD) T.
Proof.
  intros pc Rb l M MD T q n c0 b0 u rv Hpc Hh Ls8 Ls0 Ls10 Lsp H1 H2 Hrv K.
  zkeys. unfold L_LVX_L1, L_LVX_EXT, L_LEAVE in *.
  destruct Hpc as [-> | ->].
  - zstep Rfd.
    zstep Rfd.
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeL.
  - zstep Rfd.
    zsetreg (8 * (n - c0)) ltac:(symmetry; apply shiftl_3).
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg. keptc_closeL.
Qed.

Definition KS_L2 : list positive := [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 20; 21; 23; 24; 26; 27; 29; 30; 32]%positive.
Lemma stub_L2 : forall Rb l M MD T (q n c1 b1 : Z),
  m_halted MD = None ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  0 <= n - c1 -> n - c1 < 4294967296 ->
  (forall R', zget R' kS8 = b1 + 8 * (n - c1) -> zget R' kS11 = q + n -> zget R' kS2 = 0 ->
     keptc Rb l R' KS_L2 -> realizes R_segs (zcfg R_segs L_LEAVE_LD (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_LVX_L2 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c1 b1 Hh La2 La3 Ls11 H1 H2 K.
  zkeys. unfold L_LVX_L2, L_LEAVE_LD in *.
  zstep Rfd.
  zstep Rfd.
  zsetreg (8 * (n - c1)) ltac:(symmetry; apply shiftl_3).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zext32.
  zstep Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end; try zreg.
  cbv [keptc KS_L2]; split_conj; try exact I; zreg.
Qed.

Definition st_w3 (st : ist) (len off ex : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len off ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
End FXG.
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_w3 in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split;
  first [ apply mem_u32_stored; clear - Hp1 Hp2; lia_std
        | (apply mem_u64_frame || apply mem_u32_frame); [assumption | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
Lemma st_rest_set92 : forall cx st M v,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_w3 st v (t_offset st) (t_extra st)) (wbytes M (w64 (c_p cx + 108)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set96 : forall cx st M v,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_w3 st (t_length st) v (t_extra st)) (wbytes M (w64 (c_p cx + 112)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set100 : forall cx st M v,
  st_rest R_segs cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest R_segs cx (st_w3 st (t_length st) (t_offset st) v) (wbytes M (w64 (c_p cx + 116)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
End FXG.
Ltac st_prestore lem v SREST :=
  let SR1 := fresh "SR1" in
  pose proof (lem _ _ _ v SREST ltac:(cbn; lia) ltac:(cbn; lia)) as SR1;
  unfold st_w3 in SR1;
  cbn [c_p t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
       t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SR1;
  clear SREST; rename SR1 into SREST.
Ltac st_prestore_k lem k SREST :=
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
    let o := eval cbn [alookup Pos.eqb] in (alookup l k) in
    lazymatch o with
    | Some ?v => st_prestore lem v SREST
    | _ => fail "st_prestore_k: register not in the update list" k
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

End FXG.
Ltac prune_rng :=
  repeat match goal with
  | H : _ < 4294967296 |- _ => clear H | H : 0 <= _ < 18446744073709551616 |- _ => clear H | H : _ < 18446744073709551616 |- _ => clear H
  | H : - 2147483648 <= _ |- _ => clear H | H : _ < 2147483648 |- _ => clear H | H : - 2147483648 <= _ < 2147483648 |- _ => clear H
  end.
End S_DistL.

Module S_DistX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL S_Match S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_DX20 : Z := 92804.
Definition L_DXBC : Z := 92960.

Definition x_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout bits out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kT6 = -16180 /\ zget R kT4 = 30 /\
  zget R kS9 = JTAB_ADDR /\ zget R kS4 = 16209 /\ zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\
  zget R kS2 = n - cin /\ zget R kS8 = bits /\ zget R kS11 = q + cin.
End FXG.
Ltac open_xregs H := unfold x_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6 JTAB_ADDR] in H; destr_conj H.
Ltac close_xregs := unfold x_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6 JTAB_ADDR]; split_conj; zreg.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Theorem distext_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DISTEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA3 = t_extra st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DX20 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG La3 KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDE : extra <= 15 /\ 1 <= length /\ length < 65536 /\ offset < 65536)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : DISTEXT = DISTEXT -> _ |- _ => exact (H eq_refl) end).
  dand HDE as (HX15 & HL1 & HL16 & HO16). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_DX20, L_DXBC in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KBA3 KLL KRT.
  prune_rng.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (JBC : forall R' M' (ci H B off : Z),
    x_regs u p q n ob osz K0 ci cout B out R' -> zget R' kS7 = H ->
    cin <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits -> 0 <= off -> off < 98304 ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' ->
    mem_u32 R_segs M' (p + 8) DISTEXT ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes R_segs (zcfg R_segs 92960 (zupd R' []) M' MD) T).
  { intros R' M' ci H B off XR G24 Hc1 Hc2 HB1 HB2 HH1 HH2 HBc HWm Ho1 Ho2 STD' Hm' SR' RET' OUT' HL' HC' HAG'.
    open_xregs XR. cbv [kS7] in G24.
    clear S72 Hback ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET SOUT Hlens Hcodes HAG.
    pose proof STD' as STD2. open_std STD2. icx_cbn. zkeys.
    zstep Rfd.
    clear Hm'.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci H B SI0 ltac:(cbn; lia) ltac:(cbn; lia) HB1 HB2 HH1 HH2 HBc ltac:(cbn; lia)) as [SI1 ME1].
    pose proof (sinv_to_match _ _ lf cf off SI1 eq_refl Ho1 Ho2) as [SI2 ME2].
    unfold st_pull, st_dx in SI2, ME2, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2, ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (match_s _ fin MD T M0 Rx lx Mx
                (IST MATCH last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: cbv [MATCH]; assumption.
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (J80 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    zget R' kA5 = q + ci -> zget R' kA2 = n - ci -> zget R' kA4 = B -> zget R' kS7 = H -> zget R' kA3 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes R_segs (zcfg R_segs 92900 (zupd R' []) M MD) T).
  { intros R' ci H B XR G16 G13 G15 G24 G14 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. cbv [kA5 kA2 kA4 kS7 kA3] in G16, G13, G15, G24, G14. clear KL.
    repeat match goal with H : forall i : Z, _ |- _ => clear H end.
    pose proof SREST as C96. unfold st_rest in C96. icx_cbn. dand C96 as (_ & _ & _ & _ & _ & C96 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tstep1 Rfd.
    clear C96.
    zstep Rfd.
    zstep Rfd.
    clear S72 Hback.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set96 17%positive SREST.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (JBC Rx Mx ci (H / 2 ^ extra) (B - extra) (offset + Z.land H (2 ^ extra - 1))) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  destruct (Z.eq_dec extra 0) as [Hx0 | Hx1].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JBC Rx Mx cin hold bits offset) end;
      try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  zbr Rfd false.
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) 92824 92900 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end;
      try zreg; try lia; try eassumption.
    + right. split; reflexivity.
    +
      intros R' H' G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_X] in KP. cbv [kS7] in G24. destr_conj KP. zimps.
      eapply (stub_L1 93536 R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
      intros R9 E9 E27 E25 E10 HK9. cbv [keptc KS_L1] in HK9. cbv [kS8 kS11 kS2 kS1] in E9, E27, E25, E10. destr_conj HK9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
        t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hmode | exact SREST].
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G16 G13 G15 G24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_X] in KP. cbv [kA5 kA2 kA4 kS7] in G16, G13, G15, G24.
      destr_conj KP. zimps.
      eapply (J80 R' ci' H' B'); try assumption; try lia. close_xregs.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx cin hold bits) end; try zreg; try lia.
    close_xregs.
Qed.

Theorem arm_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  zkeysb. unfold L_DISTEXT in *.
  zstep Rfd.
  zstep Rfd.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : 0 <= t_extra st <= 15).
  { dand Mo as (_ & _ & _ & _ & _ & _ & _ & Mde & _). destruct (Mde Hmd) as [A _].
    unfold RNG in R. destr_conj R. split; [assumption | exact A]. }
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
    eapply (distext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end.
  - split; [exact FIX0 | split; [exact VARS | zreg]].
  - cbv [zget_l alookup Pos.eqb]. rewrite swrap32_small by lia. reflexivity.
  - exact KM0.
  - exact K.
Qed.
End FXG.
End S_DistX.

Module S_Dist.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL S_Match S_DistL S_DistX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_D8EC : Z := 92752.
Definition L_DBAD : Z := 92864.

Definition d_regs (u p ob osz : Z) (K0 : positive -> Z) (cout out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kS4 = 16209 /\
  zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\ zget R kS9 = 67008.
End FXG.
Ltac open_dregs H := unfold d_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_dregs := unfold d_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6]; split_conj; zreg.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- d_regs _ _ _ _ _ _ _ _ => close_dregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.

Theorem dist_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DIST -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_DIST (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ DIST LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HDI : 1 <= length /\ length < 65536) by mode_getr MODE_. destruct HDI as [HL1 HL16]. clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtL TOKL Cla1 Cla2 Cna ALla Slaob Slap Slap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf dc) as rdD eqn:ErdD. clear ErdD.
  prune_rng.
  zkeysb. unfold L_DIST, L_D8EC, L_DBAD, L_DLOOP1, L_D04, L_DLOOP2, L_D8BC, L_LVX_L1, L_LVX_L2 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  assert (J8EC : forall R' (ci B H e ab : Z),
    d_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = p + 7160 -> zget R' kT1 = code_op e -> zget R' kA6 = code_val e -> zget R' kA4 = code_bits e ->
    zget R' kA3 = B -> zget R' kS7 = H -> zget R' kA5 = ab -> zget R' kS10 = q + ci -> zget R' kA2 = n - ci ->
    1 <= code_bits e ->
    ((16 <= code_op e < 32 /\ 1 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 32768 /\ code_op e <= 29)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 32 = 0)) ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    realizes R_segs (zcfg R_segs 92752 (zupd R' []) M MD) T).
  { intros R' ci B H e ab DR G32 G30 G31 G10 G7 G17 G15 G14 G24 G16 G28 G13 Hbe CLS Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm.
    open_dregs DR. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G10; kcbv_in G7; kcbv_in G17; kcbv_in G15;
    kcbv_in G14; kcbv_in G24; kcbv_in G16; kcbv_in G28; kcbv_in G13.
    clear S104 S96 S72 HtD KL KLL.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (H / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    clear Hback.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
    destruct CLS as [(Hop16 & Hv1 & Hv32k & Hop29) | (H64 & H16 & H32)].
    2: {
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64.
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      unfold KBADMSG_A3, L_BADMSG_A3 in KBA3.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KBA3 Rx Mx (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                              lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
      - apply sinv_bad_of. exact SI1.
      - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                      (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                           lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
        cbn [t_mode] in MB. change (rank DIST) with 16 in MB. clear - MB ME1. lia.
      - unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      - zreg. - zreg. - zreg. - zreg. - zreg. - zreg.
      - cbv [kA3]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66314 by (symmetry; zreg) end. rewrite TW64. lia.
      - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [exact SREST | exact SRET | exact SOUT | exact HAG]. }
    pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    zbr Rfd false.
    zstep Rfd.
    zsetreg (code_op e - 16) ltac:(lia).
    zstep Rfd.
    st_prestore st_rest_set96 (code_val e) SREST.
    tstep1 Rfd.
    st_prestore_k st_rest_set100 14%positive SREST.
    tstep1 Rfd.
    clear Hmode.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_to_distext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
    unfold st_dx in SI2, ME2. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2.
    unfold L_DX20 in *.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (distext_s _ fin MD T M0 Rx lx Mx
                (IST DISTEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length (code_val e) (code_op e - 16)
                     lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [DISTEXT]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (KX1 : forall R' (H' : Z),
    zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    d_regs u p ob osz K0 cout out R' -> zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin ->
    realizes R_segs (zcfg R_segs 93492 (zupd R' []) M MD) T).
  { intros R' H' G24 HH1 HH2 HB14 HBn DR G25 G9 G27. open_dregs DR. kcbv_in G24; kcbv_in G25; kcbv_in G9; kcbv_in G27.
    clear J8EC KBA3 KLL.
    eapply (stub_L1 93492 R' [] M MD T q n cin bits u ret); [left; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
    intros R9 E9 E27 E25 E10 KP. cbv [keptc KS_L1] in KP. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (J04 : forall R' (ci B H : Z),
    d_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin -> zget R' kA5 = da -> zget R' kA7 = 2 ^ db + -1 ->
    zget R' kS10 = q + ci -> zget R' kA2 = n - ci -> zget R' kA3 = B -> zget R' kS7 = H ->
    zget R' kA6 = da + 4 * Z.land (2 ^ db + -1) H -> zget R' kA4 = code_bits (rdD (Z.land (2 ^ db + -1) H)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdD (Z.land (2 ^ db + -1) H)) <= B -> B <= 40 ->
    0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    realizes R_segs (zcfg R_segs 92524 (zupd R' []) M MD) T).
  { intros R' ci B H DR G32 G30 G31 G25 G9 G27 G16 G18 G28 G13 G14 G24 G17 G15 Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    open_dregs DR. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G9; kcbv_in G27; kcbv_in G16; kcbv_in G18;
    kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G24; kcbv_in G17; kcbv_in G15.
    clear KX1 KL.
    set (i := Z.land (2 ^ db + -1) H) in *.
    pose proof (land_mask_l' H db ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry DISTS rdD db nd i TOKD Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdD i)) as Rop. pose proof (code_val_range (rdD i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    tld4_op HtD i.
    tld4_val HtD i.
    zstep Rfd.
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_DISTS in TM as [Hb1 CLS].
      assert (Hop16 : 16 <= code_op (rdD i)).
      { destruct CLS as [(A & _) | (A64 & _ & _)]; [lia|].
        apply is_linkop_false in NL. pose proof (land_range_r (code_op (rdD i)) 64 ltac:(lia)).
        destruct (Z_lt_dec (code_op (rdD i)) 16); [|lia]. exfalso.
        assert (E : code_op (rdD i) = 0) by lia. rewrite E in A64. apply A64. reflexivity. }
      zbr Rfd true.
      zstep Rfd.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8EC Rx ci B H (rdD i)) end.
      all: jfin.
    -
      rewrite L2 in G15.
      pose proof (op_link_tests (code_op (rdD i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (db + code_op (rdD i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdD i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (db + code_op (rdD i)) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (db + code_op (rdD i)) - 1) ltac:(symmetry; apply mask_not_sllw; lia).
      set (m2 := 2 ^ (db + code_op (rdD i)) - 1) in *.
      set (v := code_val (rdD i)) in *. set (lo := code_op (rdD i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ db < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (db + lo) ltac:(lia)) as A. fold m2 in A.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r H (db + lo) ltac:(lia)) as Rm. fold m2 in Rm.
      zstep Rfd.
      zsetreg (Z.land H m2 / 2 ^ db) ltac:(symmetry; apply srlw_small; lia).
      pose proof (JR H) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'. apply term_ok_DISTS in TM2 as [Hbits2 CLS2].
      zstep Rfd.
      zsetreg (v + Z.land H m2 / 2 ^ db) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land H m2 / 2 ^ db)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      tld4_bits HtD (v + Z.land H m2 / 2 ^ db).
      zstep Rfd.
      assert (J8BC : forall R2 (ci2 B2 H2 : Z),
        d_regs u p ob osz K0 cout out R2 -> zget R2 kS11 = q + cin ->
        zget R2 kA5 = da -> zget R2 kA4 = db -> zget R2 kA6 = v -> zget R2 kS2 = p + 7160 ->
        zget R2 kA2 = n - ci -> zget R2 kA3 = B -> zget R2 kS10 = q + ci ->
        zget R2 kT5 = q + ci2 -> zget R2 kA7 = n - ci2 -> zget R2 kT0 = B2 -> zget R2 kS7 = H2 ->
        zget R2 kT3 = da + 4 * (v + Z.land H2 m2 / 2 ^ db) -> zget R2 kT2 = code_bits (rdD (v + Z.land H2 m2 / 2 ^ db)) ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> db + code_bits (rdD (v + Z.land H2 m2 / 2 ^ db)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes R_segs (zcfg R_segs 92708 (zupd R2 []) M MD) T).
      { intros R2 ci2 B2 H2 DR2 Q27 Q16 Q15 Q17 Q10 Q13 Q14 Q28 Q31 Q18 Q6 Q24 Q29 Q8 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        open_dregs DR2. kcbv_in Q27; kcbv_in Q16; kcbv_in Q15; kcbv_in Q17; kcbv_in Q10;
        kcbv_in Q13; kcbv_in Q14; kcbv_in Q28; kcbv_in Q31; kcbv_in Q18; kcbv_in Q6; kcbv_in Q24; kcbv_in Q29; kcbv_in Q8.
        clear KLL.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ db) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdD (v + j2))) as Rb2.
        zstep Rfd.
        tld4_op HtD (v + j2).
        tld4_val HtD (v + j2).
        zstep Rfd.
        zsetreg (H2 / 2 ^ db) ltac:(symmetry; apply (srl_hold H2 B2); lia).
        pose proof (hold_shr_bound H2 B2 db ltac:(lia) ltac:(lia)) as HH2'.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_DISTS in TM3 as [Hbits3 CLS3].
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (J8EC Rx ci2 (B2 - db) (H2 / 2 ^ db) (rdD (v + j2))) end.
        all: jfin. }
      destruct (Z_lt_dec B (db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)))) as [Hneed | Hok].
      + zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (d_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n da nd db lo v m2 ci B ci B H fin rdD Hh) end.
        all: jfin.
        *
          intros R5 H' Q24 HH1' HH2' HB29 HBn KP. cbv [keptc KS_D2] in KP. kcbv_in Q24. destr_conj KP. zimps.
          clear J8BC J8EC SUB JR.
          eapply (stub_L2 R5 [] M MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 E9 E27 E25 KP9. cbv [keptc KS_L2] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25. destr_conj KP9. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
            t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- exact SOUT.
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        *
          intros R5 ci' B' H' Q31 Q18 Q6 Q30 Q24 Q29 Q8 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D2] in KP.
          kcbv_in Q31; kcbv_in Q18; kcbv_in Q6; kcbv_in Q30; kcbv_in Q24; kcbv_in Q29; kcbv_in Q8. destr_conj KP. zimps.
          eapply (J8BC R5 ci' B' H'). all: jfin.
      + zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8BC Rx ci B H) end. all: jfin. }
  clear KBA3 KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & _ & C112 & _ & C124 & _).
  rewrite <- Eda in C112. clear Eda.
  tstep1 Rfd.
  zstep Rfd.
  clear C112 C124.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ db + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold db ltac:(lia)) as Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land (2 ^ db + -1) hold) TOKD Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ db + -1) hold) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits HtD (Z.land (2 ^ db + -1) hold).
  destruct (Z_lt_dec bits (code_bits (rdD (Z.land (2 ^ db + -1) hold)))) as [Hneed | Hok].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (d_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n da nd db (2 ^ db + -1) cin bits cin bits hold fin rdD Hh) end.
    all: jfin.
    + intros R' H' G24 HH1' HH2' HB14 HBn KP. cbv [keptc KS_D1] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_D1] in KP.
      kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G6; kcbv_in G24; kcbv_in G15; kcbv_in G17. destr_conj KP. zimps.
      eapply (J04 R' ci' B' H'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx cin bits hold) end. all: jfin.
Qed.

Theorem arm_DIST : arm_stmt L_DIST DIST.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply dist_s; try eassumption.
Qed.
End FXG.
End S_Dist.

Module S_LenL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_LLOOP1 : Z := 91996.
Definition L_L40 : Z := 92068.
Definition L_LLOOP2 : Z := 92164.
Definition L_L700 : Z := 92268.

Definition KS_E1 : list positive := [2; 3; 4; 5; 9; 10; 11; 12; 16; 17; 19; 20; 21; 23; 25; 26; 28; 29; 30; 32]%positive.
Definition KS_E2 : list positive := [2; 3; 4; 5; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 25; 26; 27; 28]%positive.
End FXG.
Ltac keptc_close ::= cbv [keptc KS_D1 KS_D2 KS_X KS_E1 KS_E2 KS_L1 KS_L2]; split_conj; try exact I; zreg.
Ltac keptc_chain HK ::= cbv [keptc KS_D1 KS_D2 KS_X KS_E1 KS_E2 KS_L1 KS_L2] in HK |- *; destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Lemma l_loop1 : forall (N : nat) Rb l M MD T (q n la na lb lm c0 b0 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA5 = la -> zget_l Rb l kA6 = lm -> zget_l Rb l kA2 = n - ci -> zget_l Rb l kT1 = q + ci ->
  zget_l Rb l kT0 = B -> zget_l Rb l kA3 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kA4 = code_bits (rdL (Z.land lm H)) -> zget_l Rb l kA7 = la + 4 * Z.land lm H ->
  zget_l Rb l kS2 = n - c0 -> zget_l Rb l kS8 = b0 -> zget_l Rb l kS11 = q + c0 ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdL (Z.land lm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  lm = 2 ^ lb - 1 -> 1 <= lb -> lb <= 15 -> 2 ^ lb <= na -> tab_ok LENS rdL lb na = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_E1 ->
     realizes R_segs (zcfg R_segs L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kS10 = q + ci' -> zget R' kA2 = n - ci' -> zget R' kA3 = B' -> zget R' kT0 = B' -> zget R' kS7 = H' ->
     zget R' kA4 = code_bits (rdL (Z.land lm H')) -> zget R' kA7 = la + 4 * Z.land lm H' ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdL (Z.land lm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E1 ->
     realizes R_segs (zcfg R_segs L_L40 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_LLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lm c0 b0 ci B H fin rdL Hh La5 La6 La2 Lt1 Lt0 La3 Ls7 La4 La7 Ls8 Ls0 Ls10
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP1, L_L40, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb.
  pose proof (land_mask_l H lb ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_l H' lb ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry LENS rdL lb na (Z.land lm H') TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land lm H') ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits Htab (Z.land lm H').
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (rdL (Z.land lm H')))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lm c0 b0 (ci + 1) (B + 8) H' fin rdL Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G28 G13 G14 G6 G24 G15 G17 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.


Lemma l_loop2 : forall (N : nat) Rb l M MD T (q n la na lb lo v m2 c1 b1 ci B H : Z) (fin rdL : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kT2 = m2 -> zget_l Rb l kA6 = lb -> zget_l Rb l kA7 = v -> zget_l Rb l kA5 = la ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  zget_l Rb l kT0 = n - ci -> zget_l Rb l kS1 = q + ci -> zget_l Rb l kT4 = B -> zget_l Rb l kT1 = B -> zget_l Rb l kS7 = H ->
  zget_l Rb l kT5 = la + 4 * (v + Z.land H m2 / 2 ^ lb) -> zget_l Rb l kT3 = code_bits (rdL (v + Z.land H m2 / 2 ^ lb)) ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < lb + code_bits (rdL (v + Z.land H m2 / 2 ^ lb)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (lb + lo) - 1 -> 1 <= lb -> lb <= 15 -> 1 <= lo -> lo <= 15 - lb -> 0 <= v -> v + 2 ^ lo <= na -> na <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdL (v + j))) = false /\ term_ok LENS (15 - lb) (rdL (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= la -> la + 4 * na <= 140737488355328 ->
  mem_arr 1 R_segs M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 R_segs M la na rdL ->
  (forall R' (H' : Z),
     zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_E2 ->
     realizes R_segs (zcfg R_segs L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     zget R' kT6 = q + ci' -> zget R' kT0 = n - ci' -> zget R' kT1 = B' -> zget R' kT4 = B' -> zget R' kS7 = H' ->
     zget R' kT5 = la + 4 * (v + Z.land H' m2 / 2 ^ lb) -> zget R' kT3 = code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_E2 ->
     realizes R_segs (zcfg R_segs L_L700 (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_LLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n la na lb lo v m2 c1 b1 ci B H fin rdL Hh Lt2 La6 La7 La5 La2 La3 Ls11
    Lt0 Ls0 Lt4 Lt1 Ls7 Lt5 Lt3 HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  zkeys. unfold L_LLOOP2, L_L700, L_LVX_L2 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 lb ltac:(lia)) as HPdb. pose proof (pow2_15 lo ltac:(lia)) as HPlo.
  assert (HPm : 1 <= 2 ^ (lb + lo) <= 32768) by (apply pow2_15; lia).
  assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
  { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. rewrite <- Hm2 in A.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
  pose proof (JR H) as Rj0.
  destruct (SUB _ Rj0) as [_ TM0]. apply term_ok_LENS in TM0 as [Hbits0 _].
  assert (HB29 : B <= 29) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_close. }
  zbr Rfd false.
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  tld1 Hin ci Rfin.
  zstep Rfd.
  zsetreg (fin ci * 2 ^ B) ltac:(symmetry; apply shl_byte; lia).
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  zstep Rfd.
  zsetreg (H + fin ci * 2 ^ B) ltac:(lia).
  set (H' := H + fin ci * 2 ^ B) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1.
  zstep Rfd.
  pose proof (land_mask_r H' (lb + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  zstep Rfd.
  zsetreg (Z.land H' m2 / 2 ^ lb) ltac:(symmetry; apply srlw_small; lia).
  pose proof (JR H') as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_LENS in TM1 as [Hbits1 _].
  zstep Rfd.
  zsetreg (v + Z.land H' m2 / 2 ^ lb) ltac:(lia).
  zstep Rfd.
  zstep Rfd.
  zsetreg (4 * (v + Z.land H' m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
  zstep Rfd.
  tld4_bits Htab (v + Z.land H' m2 / 2 ^ lb).
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (lb + code_bits (rdL (v + Z.land H' m2 / 2 ^ lb)))) as [Hmore | Hdone].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n la na lb lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdL Hh) end;
      try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' G31 G18 G6 G30 G24 G29 G8 X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end;
      try zreg; try lia.
    all: keptc_close.
Qed.


Definition st_le (st : ist) (m len ex : Z) : ist :=
  IST m (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len (t_offset st) ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_len_set : forall cx st lf cf m len,
  sinv cx st lf cf -> t_mode st = LEN -> (m = LEN \/ m = LIT \/ m = TYPE) -> 0 <= len -> len < 4294967296 ->
  sinv cx (st_le st m len (t_extra st)) lf cf.
Proof.
  intros cx st lf cf m len SI Hm Hm' Hl1 Hl2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [| split; [exact W | split; [prog_transfer P|]]].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
Qed.

Lemma sinv_to_lenext : forall cx st lf cf len ex,
  sinv cx st lf cf -> t_mode st = LEN -> 1 <= len -> len <= 32768 -> 0 <= ex -> ex <= 15 ->
  sinv cx (st_le st LENEXT len ex) lf cf /\ meas cx (st_le st LENEXT len ex) < meas cx st.
Proof.
  intros cx st lf cf len ex SI Hm Hl1 Hl2 He1 He2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2 He1 He2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma sinv_to_dist : forall cx st lf cf len,
  sinv cx st lf cf -> t_mode st = LENEXT -> 1 <= len -> len < 65536 ->
  sinv cx (st_le st DIST len (t_extra st)) lf cf /\ meas cx (st_le st DIST len (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf len SI Hm Hl1 Hl2.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LENEXT = HEAD \/ LENEXT = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LENEXT -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  split; [split; [| split; [exact W | split; [prog_transfer P|]]] |].
  - clear W P Mf Mlive. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | intros _; clear - Hl1 Hl2; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Lemma st_rest_le : forall cx st M m len ex,
  st_rest R_segs cx (st_w3 st len (t_offset st) ex) M -> st_rest R_segs cx (st_le st m len ex) M.
Proof. intros cx st M m len ex H. destruct cx, st. exact H. Qed.
End FXG.
End S_LenL.

Module S_LenX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL S_Match S_DistL S_DistX S_Dist S_LenL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_LX34 : Z := 87124.
Definition L_L770 : Z := 92376.
Definition L_L778 : Z := 92384.

End FXG.
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
End FXG.
Ltac jfin :=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- x_regs _ _ _ _ _ _ _ _ _ _ _ _ => close_xregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac st_cbn_in H := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in H.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Theorem len_to_dist : forall cx fin MD T M0 Rb l M st lf cf (m len : Z),
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> 1 <= len -> len < 65536 ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA6 = len -> zget_l Rb l kT1 = c_p cx + 7160 ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) m -> st_rest R_segs cx (st_w3 st len (t_offset st) (t_extra st)) M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_L778 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf m len CX Hh Hfin Hmd SI Hl1 Hl2 RG La6 Lt1 STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  pose proof (sinv_to_dist cx st lf cf len SI Hmd Hl1 Hl2) as [SI1 ME1].
  pose proof (st_rest_le cx st M DIST len (t_extra st) SREST) as SR1. clear SREST.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode. unfold st_le in SI1, ME1, SR1. st_cbn_in SI1. st_cbn_in ME1. st_cbn_in SR1.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  zkeysb. unfold L_L778, L_DIST in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hm.
  tstep1 Rfd.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (dist_s _ fin MD T M0 Rx lx Mx
              (IST DIST last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [DIST]; assumption | exact SR1 | exact SRET | exact SOUT | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.

Theorem len_70 : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) LENEXT -> st_rest R_segs cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_L770 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  assert (HLE : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { dand SI as (_ & _ & _ & Mo). clear - Mo Hmd. unfold MODE in Mo.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  dand HLE as (HX15 & HL1 & HL32).
  pose proof CX as CX0. pose proof RG as RG0. pose proof STD as STD0.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn.
  zkeysb. unfold L_L770, L_L778 in *. cbv [JTAB_ADDR] in *.
  pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  pose proof (proj1 SI) as R. unfold RNG in R. icx_cbn. dand R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [RL1 RL2] & _).
  tstep1 Rfd.
  zstep Rfd.
  clear C92 S72.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_to_dist _ fin MD T M0 Rx lx Mx
              (IST LENEXT last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf LENEXT length CX0 Hh Hfin eq_refl SI) end.
  - lia.
  - lia.
  - split; [| split]; [unfold s_fix | unfold s_vars | ]; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - zreg.
  - icx_cbn. zreg.
  - exact STD0.
  - exact Hm.
  - unfold st_w3; icx_cbn. exact SREST.
  - exact SRET.
  - exact SOUT.
  - exact Hlens.
  - exact Hcodes.
  - exact HP0.
  - exact K.
Qed.

Theorem lenext_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENEXT -> sinv cx st lf cf -> t_extra st <> 0 ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA3 = t_extra st ->
  s_std cx fin M -> mem_u32 R_segs M (c_p cx + 8) LENEXT -> st_rest R_segs cx st M ->
  s_ret cx st M -> s_out cx st M -> mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf -> mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf ->
  mpostL R_segs M0 M (fp_loop cx) ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LX34 (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI Hx1 RG La3 STD Hm SREST SRET SOUT Hlens Hcodes HP0 K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  assert (HLE : extra <= 15 /\ 1 <= length /\ length <= 32768)
    by (clear - MODE_; unfold MODE in MODE_; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
        match goal with H : LENEXT = LENEXT -> _ |- _ => exact (H eq_refl) end).
  dand HLE as (HX15 & HL1 & HL32). clear MODE_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  prune_rng.
  zkeysb. unfold L_LX34, L_L778, L_LXLOOP, L_LX60, L_LVX_EXT in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KRL KB11 KB10 KBA3 KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & _).
  destruct (mem_wr_u32_exists_R M (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (vb & Hback & Rvb).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  assert (J60 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    zget R' kA5 = q + ci -> zget R' kA2 = n - ci -> zget R' kA4 = B -> zget R' kS7 = H -> zget R' kA3 = extra ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes R_segs (zcfg R_segs 89320 (zupd R' []) M MD) T).
  { intros R' ci H B XR G16 G13 G15 G24 G14 Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. kcbv_in G16; kcbv_in G13; kcbv_in G15; kcbv_in G24; kcbv_in G14. clear KL.
    repeat match goal with H : forall i : Z, _ |- _ => lazymatch H with Hfin => fail | _ => clear H end end.
    pose proof SREST as C92. unfold st_rest in C92. icx_cbn. dand C92 as (_ & _ & _ & _ & C92 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tstep1 Rfd.
    clear C92.
    zstep Rfd.
    zstep Rfd.
    clear S72 Hback.
    zstep Rfd.
    zstep Rfd.
    zsetreg (2 ^ extra - 1) ltac:(symmetry; apply mask_not_sllw; lia).
    zstep Rfd.
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zsetreg (H / 2 ^ extra) ltac:(symmetry; apply (srl_hold H B); lia).
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    zstep Rfd.
    st_prestore_k st_rest_set92 17%positive SREST.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ extra) (B - extra) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (len_to_dist _ fin MD T M0 Rx lx Mx
                (IST LENEXT last flags ci cout (H / 2 ^ extra) (B - extra) out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf LENEXT (length + Z.land H (2 ^ extra - 1)) CX0 Hh Hfin eq_refl SI1) end.
    - lia.
    - lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - icx_cbn. zreg.
    - close_std.
    - icx_cbn. exact Hm.
    - unfold st_w3; icx_cbn. exact SREST.
    - exact SRET.
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG.
    - eapply KALL_mono; [| exact K]. clear - ME1. lia. }
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) 87140 89320 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end.
    1: left; split; reflexivity.
    all: jfin.
    +
      intros R' H' G24 HH1 HH2 HB14 HBn KP. cbv [keptc KS_X] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (stub_L1 93536 R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
      intros R9 E9 E27 E25 E10 KP9. cbv [keptc KS_L1] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP9. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. st_cbn_in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hm | exact SREST].
      * exact SOUT.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' G16 G13 G15 G24 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_X] in KP. kcbv_in G16; kcbv_in G13; kcbv_in G15; kcbv_in G24.
      destr_conj KP. zimps.
      eapply (J60 R' ci' H' B'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J60 Rx cin hold bits) end. all: jfin.
Qed.

Theorem arm_LENEXT : arm_stmt L_LENEXT LENEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : t_extra st <= 15 /\ 1 <= t_length st /\ t_length st <= 32768).
  { clear - Mo Hmd. unfold MODE in Mo. repeat match goal with H : _ /\ _ |- _ => destruct H end.
    match goal with H : t_mode st = LENEXT -> _ |- _ => exact (H Hmd) end. }
  assert (HX0 : 0 <= t_extra st) by (unfold RNG in R; destr_conj R; assumption). clear R Mo.
  zkeysb. unfold L_LENEXT, L_LX34, L_L770 in *.
  tstep1 Rfd.
  destruct (Z.eq_dec (t_extra st) 0) as [Hx0 | Hx1].
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_70 cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end.
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + exact SOUT.
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (lenext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI Hx1) end.
    + split; [exact FIX0 | split; [exact VARS | zreg]].
    + zreg.
    + exact STD.
    + rewrite <- Hmd. exact Hmode.
    + exact SREST.
    + exact SRET.
    + exact SOUT.
    + exact Hlens.
    + exact Hcodes.
    + exact HP0.
    + exact K.
Qed.
End FXG.
End S_LenX.

Module S_Len.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S.SBase.
Import S_MatchL S_Match S_DistL S_DistX S_Dist S_LenL S_LenX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_LSLOW : Z := 91932.
Definition L_L28 : Z := 92304.

Definition e_regs (u p ob osz : Z) (K0 : positive -> Z) (cout out : Z) (R : tree Z) : Prop :=
  zget R kSP = u + -224 /\ zget R kGP = K0 kGP /\ zget R kTP = K0 kTP /\ zget R kS0 = p /\
  zget R kA0 = u /\ zget R kA1 = 0 /\ zget R kS6 = p + 168 /\ zget R kS4 = 16209 /\
  zget R kS3 = ob + cout /\ zget R kRA = osz - cout /\ zget R kS9 = 67008.
End FXG.
Ltac open_eregs H := unfold e_regs in H; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6] in H; destr_conj H.
Ltac close_eregs := unfold e_regs; cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS1 kS2 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS0 kS11 kS10 kT3 kT4 kT5 kT6]; split_conj; zreg.
Ltac jfin ::=
  lazymatch goal with
  | |- zget _ _ = _ => zreg
  | |- zget_l _ _ _ = _ => zreg
  | |- e_regs _ _ _ _ _ _ _ _ => close_eregs
  | |- keptc _ _ _ _ => keptc_close
  | |- realizes _ _ _ => idtac
  | |- forall _, _ => try assumption
  | |- _ \/ _ => assumption
  | |- mem_arr _ _ _ _ _ _ => assumption
  | |- tab_ok _ _ _ _ = true => assumption
  | |- m_halted _ = _ => assumption
  | |- s_std _ _ _ => close_std
  | |- st_rest _ _ _ _ => assumption
  | |- s_ret _ _ _ => assumption
  | |- s_out _ _ _ => assumption
  | |- framed _ _ => assumption
  | |- mem_u32 _ _ _ _ => assumption
  | |- mem_u64 _ _ _ _ => assumption
  | |- mem_wr _ _ _ _ => assumption
  | |- _ => first [assumption | lia]
  end.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.
Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.

Theorem len_slow_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LSLOW (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_). clear WIN_.
  pose proof KM as KM0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold PROG, Wm in PROG_; icx_cbn. dand PROG_ as (PR1 & PR2 & PR3).
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  clear HtD TOKD Cda1 Cda2 Cnd ALda Sdaob Sdap Sdap2.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (rdc cf lc) as rdL eqn:ErdL. clear ErdL.
  prune_rng.
  zkeysb. unfold L_LSLOW, L_L28, L_LLOOP1, L_L40, L_LLOOP2, L_L700, L_LVX_L1, L_LVX_L2, L_L770, L_LX34 in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD10 KD00 KSM KRA1 KRL KB11 KB10 KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & S72 & _).
  assert (HPb : 1 <= 2 ^ bits <= 2 ^ 40) by (split; [pose proof (pow2_pos bits ltac:(lia)); lia | apply pow2_le; lia]).
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & C104 & _ & C120 & _).
  rewrite <- Ela in C104. clear Ela.
  tstep1 Rfd.
  zstep Rfd.
  clear C104 C120.
  zstep Rfd.
  tstep1 Rfd.
  assert (J28 : forall R' M' (ci B Hd e lbv : Z),
    e_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS11 = p + 7160 -> zget R' kT2 = code_op e -> zget R' kA7 = code_val e -> zget R' kA4 = code_bits e ->
    zget R' kA6 = lbv -> zget R' kA3 = B -> zget R' kS7 = Hd -> zget R' kS10 = q + ci -> zget R' kA2 = n - ci ->
    1 <= code_bits e ->
    ((code_op e = 0 /\ code_val e < 256)
     \/ (16 <= code_op e < 32 /\ 3 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 258 /\ code_op e <= 21)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0)) ->
    0 <= lbv -> lbv <= 15 ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' -> mem_u32 R_segs M' (p + 8) LEN ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 R_segs M' (p + 168) 320 lf -> mem_arr 4 R_segs M' (p + 1384) 1444 cf ->
    mem_wr R_segs M' p 7176 ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes R_segs (zcfg R_segs 92304 (zupd R' []) M' MD) T).
  { intros R' M' ci B Hd e lbv ER G32 G30 G31 G25 G8 G18 G15 G17 G14 G24 G28 G13 Hbe CLS Hlv1 Hlv2 Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm
           STD' Hm' SR' RET' OUT' HL' HC' Wp' HAG'.
    open_eregs ER. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G8; kcbv_in G18; kcbv_in G15;
    kcbv_in G17; kcbv_in G14; kcbv_in G24; kcbv_in G28; kcbv_in G13.
    clear S104 S96 S72 HtL KL KLL ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET SOUT Hlens Hcodes HAG.
    repeat match goal with Hd : forall i : Z, _ |- _ => lazymatch Hd with Hfin => fail | _ => clear Hd end end.
    repeat match goal with Hd : context [M] |- _ => clear Hd end.
    rename STD' into STD. rename Hm' into Hmode. rename SR' into SREST. rename RET' into SRET. rename OUT' into SOUT.
    rename HL' into Hlens. rename HC' into Hcodes. rename HAG' into HAG.
    pose proof STD as STD2. open_std STD2. icx_cbn. zkeys.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    zsetreg (Hd / 2 ^ code_bits e) ltac:(symmetry; apply (srl_hold Hd B); lia).
    pose proof (hold_shr_bound Hd B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_u32_exists_R Mx (p + 7164) ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (vb & Hback & Rvb) end. clear Hback.
    tstep1 Rfd.
    st_prestore st_rest_set92 (code_val e) SREST.
    tstep1 Rfd.
    pose proof (sinv_pull _ _ lf cf ci (Hd / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. st_cbn_in SI1. st_cbn_in ME1.
    unfold KDISP, L_DISP in KD. unfold KBADMSG_A3, L_BADMSG_A3 in KBA3. zkeys.
    destruct CLS as [[Hop0 Hv256] | [(Hop16 & Hv3 & Hv258 & Hop21) | [H64 H16]]].
    -
      zbr Rfd true.
      zstep Rfd.
      clear Hmode.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_len_set _ _ lf cf LIT (code_val e) SI1 eq_refl ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KD Rx Mx (IST LIT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI2) end.
      + clear - ME1. unfold meas, Wm in *. icx_cbn. change (rank LIT) with 13 in *. change (rank LEN) with 18 in *. lia.
      + unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
      + unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
        all: first [cbv [LIT]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
    -
      pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
      rewrite shiftl_1_pow in Hv258 by lia. pose proof (pow2_15 (code_op e - 16) ltac:(lia)) as HPx.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (code_op e + -16) ltac:(lia).
      zstep Rfd.
      st_prestore_k st_rest_set100 14%positive SREST.
      tstep1 Rfd.
      clear Hmode.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_to_lenext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
      unfold st_le in SI2, ME2. st_cbn_in SI2. st_cbn_in ME2.
      destruct (Z.eq_dec (code_op e - 16) 0) as [Hx0 | Hx1].
      + zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (len_70 _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end.
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. exact SREST.
        * exact SRET.
        * exact SOUT.
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
      + zbr Rfd false.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (lenext_s _ fin MD T M0 Rx lx Mx
                    (IST LENEXT last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset (code_op e - 16)
                         lc dc lb db ncode nlen ndist shave nx whave wnext)
                    lf cf CX0 Hh Hfin eq_refl SI2) end.
        * icx_cbn. exact Hx1.
        * unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * icx_cbn. zreg.
        * close_std.
        * icx_cbn. cbv [LENEXT]. assumption.
        * icx_cbn. exact SREST.
        * exact SRET.
        * exact SOUT.
        * exact Hlens.
        * exact Hcodes.
        * exact HAG.
        * eapply KALL_mono; [| exact K]. clear - ME1 ME2. lia.
    -
      assert (Tnz : code_op e <> 0) by (intros E; rewrite E in H64; apply H64; reflexivity).
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64. pose proof (land_range_r (code_op e) 32 ltac:(lia)) as R32.
      zbr Rfd false.
      zstep Rfd.
      pose proof (sinv_len_set _ _ lf cf LEN (code_val e) SI1 eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      unfold st_le in SI2. st_cbn_in SI2.
      destruct (Z.eq_dec (Z.land (code_op e) 32) 0) as [H32 | H32].
      +
        zbr Rfd false.
        zstep Rfd.
        zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KBA3 Rx Mx (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                                lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end.
        * apply sinv_bad_of. exact SI2.
        * pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                        (IST LEN last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                             lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
          cbn [t_mode] in MB. change (rank LEN) with 18 in MB. clear - MB ME1. unfold meas, Wm in *. icx_cbn. lia.
        * unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * zreg. * zreg. * zreg. * zreg. * zreg. * zreg.
        * cbv [kA3]. lazymatch goal with |- 0 <= ?x < _ => replace x with 66608 by (symmetry; zreg) end. rewrite TW64. lia.
        * unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
          all: first [exact SREST | exact SRET | exact SOUT | exact HAG].
      +
        zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        clear Hmode.
        tstep1 Rfd.
        repeat match goal with Hd : mem_u32 _ _ (p + 7164) _ |- _ => clear Hd end.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        pose proof (sinv_len_set _ _ lf cf TYPE (code_val e) SI1 eq_refl ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI3.
        unfold st_le in SI3. st_cbn_in SI3.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (KD Rx Mx (IST TYPE last flags ci cout (Hd / 2 ^ code_bits e) (B - code_bits e) out ret (code_val e) offset extra
                               lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf SI3) end.
        * clear - HWm Hbe. unfold meas, Wm. icx_cbn. change (rank TYPE) with 24. change (rank LEN) with 18. lia.
        * unfold s_regs_disp, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
        * unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
          all: first [cbv [TYPE]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG]. }
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => rename Mx into M1 end.
  match goal with Hb : mem_u32 _ M1 (p + 7164) 0 |- _ => rename Hb into Hback0 end.
  assert (KX1 : forall R' (H' : Z),
    zget R' kS7 = H' -> 0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    e_regs u p ob osz K0 cout out R' -> zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin ->
    realizes R_segs (zcfg R_segs 93492 (zupd R' []) M1 MD) T).
  { intros R' H' G24 HH1 HH2 HB14 HBn ER G25 G9 G27. open_eregs ER. kcbv_in G24; kcbv_in G25; kcbv_in G9; kcbv_in G27.
    clear J28 KBA3 KLL KD.
    eapply (stub_L1 93492 R' [] M1 MD T q n cin bits u ret); [left; reflexivity | exact Hh | zreg | zreg | zreg | zreg | lia | lia | exact SRET |].
    intros R9 E9 E27 E25 E10 KP. cbv [keptc KS_L1] in KP. kcbv_in E9; kcbv_in E27; kcbv_in E25; kcbv_in E10. destr_conj KP. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. st_cbn_in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M1 _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SOUT.
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (J40 : forall R' (ci B Hd : Z),
    e_regs u p ob osz K0 cout out R' -> zget R' kT6 = -16180 -> zget R' kT4 = 30 -> zget R' kS9 = 67008 ->
    zget R' kS2 = n - cin -> zget R' kS8 = bits -> zget R' kS11 = q + cin -> zget R' kA5 = la -> zget R' kA6 = 2 ^ lb + -1 ->
    zget R' kS10 = q + ci -> zget R' kA2 = n - ci -> zget R' kA3 = B -> zget R' kS7 = Hd ->
    zget R' kA7 = la + 4 * Z.land (2 ^ lb + -1) Hd -> zget R' kA4 = code_bits (rdL (Z.land (2 ^ lb + -1) Hd)) ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdL (Z.land (2 ^ lb + -1) Hd)) <= B -> B <= 40 ->
    0 <= Hd -> Hd < 2 ^ B -> B <= 8 * ci ->
    realizes R_segs (zcfg R_segs 92068 (zupd R' []) M1 MD) T).
  { intros R' ci B Hd ER G32 G30 G31 G25 G9 G27 G16 G17 G28 G13 G14 G24 G18 G15 Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    open_eregs ER. kcbv_in G32; kcbv_in G30; kcbv_in G31; kcbv_in G25; kcbv_in G9; kcbv_in G27; kcbv_in G16; kcbv_in G17;
    kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G24; kcbv_in G18; kcbv_in G15.
    clear KX1 KL KD KBA3.
    set (i := Z.land (2 ^ lb + -1) Hd) in *.
    pose proof (land_mask_l' Hd lb ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry LENS rdL lb na i TOKL Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdL i)) as Rop. pose proof (code_val_range (rdL i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    zstep Rfd.
    tld4_op HtL i.
    tld4_val HtL i.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_LENS in TM as [Hb1 CLS].
      apply is_linkop_false in NL.
      assert (Hterm : code_op (rdL i) = 0 \/ 16 <= code_op (rdL i)).
      { destruct CLS as [(A & _) | [(A & _) | (A64 & _)]]; [lia | lia |].
        pose proof (land_range_r (code_op (rdL i)) 64 ltac:(lia)).
        destruct (Z.eq_dec (code_op (rdL i)) 0) as [E|E]; [left; exact E|]. right.
        destruct (Z_lt_dec (code_op (rdL i)) 16); [|lia]. exfalso. apply NL. lia. }
      destruct Hterm as [E | E];
        [ assert (Hbr : (code_op (rdL i) + -1) mod 18446744073709551616 = 18446744073709551615) by (rewrite E; reflexivity)
        | idtac ];
        zbr Rfd true;
        zstep Rfd;
        zstep Rfd;
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (J28 Rx Mx ci B Hd (rdL i) 0) end;
        jfin.
    -
      rewrite L2 in G15.
      pose proof (op_link_tests (code_op (rdL i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (lb + code_op (rdL i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdL i)) ltac:(lia)) as HPlo.
      zbr Rfd false.
      zstep Rfd.
      zsetreg (lb + code_op (rdL i)) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zsetreg (2 ^ (lb + code_op (rdL i)) + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
      set (m2 := 2 ^ (lb + code_op (rdL i)) + -1) in *.
      set (v := code_val (rdL i)) in *. set (lo := code_op (rdL i)) in *.
      assert (JR : forall Hx, 0 <= Z.land Hx m2 / 2 ^ lb < 2 ^ lo).
      { intros Hx. pose proof (land_mask_r Hx (lb + lo) ltac:(lia)) as A. replace (2 ^ (lb + lo) - 1) with m2 in A by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      zstep Rfd.
      pose proof (land_mask_r Hd (lb + lo) ltac:(lia)) as Rm. replace (2 ^ (lb + lo) - 1) with m2 in Rm by lia.
      zstep Rfd.
      zsetreg (Z.land Hd m2 / 2 ^ lb) ltac:(rewrite <- L2; symmetry; apply srlw_small; lia).
      pose proof (JR Hd) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'. apply term_ok_LENS in TM2 as [Hbits2 CLS2].
      zstep Rfd.
      zsetreg (v + Z.land Hd m2 / 2 ^ lb) ltac:(lia).
      zstep Rfd.
      zstep Rfd.
      zsetreg (4 * (v + Z.land Hd m2 / 2 ^ lb)) ltac:(symmetry; apply zext32_shift30; lia).
      zstep Rfd.
      tld4_bits HtL (v + Z.land Hd m2 / 2 ^ lb).
      zstep Rfd.
      assert (J700 : forall R2 (ci2 B2 H2 : Z),
        e_regs u p ob osz K0 cout out R2 ->
        zget R2 kA5 = la -> zget R2 kA6 = lb -> zget R2 kA7 = v -> zget R2 kS11 = p + 7160 -> zget R2 kA4 = lb ->
        zget R2 kA2 = n - ci -> zget R2 kA3 = B -> zget R2 kS10 = q + ci ->
        zget R2 kT6 = q + ci2 -> zget R2 kT0 = n - ci2 -> zget R2 kT1 = B2 -> zget R2 kS7 = H2 ->
        zget R2 kT5 = la + 4 * (v + Z.land H2 m2 / 2 ^ lb) -> zget R2 kT3 = code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb)) ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> lb + code_bits (rdL (v + Z.land H2 m2 / 2 ^ lb)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes R_segs (zcfg R_segs 92268 (zupd R2 []) M1 MD) T).
      { intros R2 ci2 B2 H2 ER2 Q16 Q17 Q18 Q25 Q15 Q13 Q14 Q28 Q32 Q6 Q7 Q24 Q31 Q29 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        open_eregs ER2. kcbv_in Q16; kcbv_in Q17; kcbv_in Q18; kcbv_in Q25; kcbv_in Q15; kcbv_in Q13; kcbv_in Q14;
        kcbv_in Q28; kcbv_in Q32; kcbv_in Q6; kcbv_in Q7; kcbv_in Q24; kcbv_in Q31; kcbv_in Q29.
        clear KLL CLS2 TM2' NL2 Hbits2 Rj Rm.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ lb) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdL (v + j2))) as Rb2.
        tld4_op HtL (v + j2).
        tld4_val HtL (v + j2).
        zstep Rfd.
        zsetreg (H2 / 2 ^ lb) ltac:(symmetry; apply (srl_hold H2 B2); lia).
        pose proof (hold_shr_bound H2 B2 lb ltac:(lia) ltac:(lia)) as HH2'.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_LENS in TM3 as [Hbits3 CLS3].
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
          eapply (J28 Rx Mx ci2 (B2 - lb) (H2 / 2 ^ lb) (rdL (v + j2)) lb) end.
        all: jfin. }
      destruct (Z_lt_dec B (lb + code_bits (rdL (v + Z.land Hd m2 / 2 ^ lb)))) as [Hneed | Hok].
      + zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (l_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n la na lb lo v m2 ci B ci B Hd fin rdL Hh) end.
        all: jfin.
        *
          intros R5 H' Q24 HH1' HH2' HB29 HBn KP. cbv [keptc KS_E2] in KP. kcbv_in Q24. destr_conj KP. zimps.
          clear J700 J28 SUB JR.
          eapply (stub_L2 R5 [] M1 MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 E9 E27 E25 KP9. cbv [keptc KS_L2] in KP9. kcbv_in E9; kcbv_in E27; kcbv_in E25. destr_conj KP9. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. st_cbn_in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M1 _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- exact SOUT.
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        *
          intros R5 ci' B' H' Q32 Q6 Q7 Q30 Q24 Q31 Q29 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E2] in KP.
          kcbv_in Q32; kcbv_in Q6; kcbv_in Q7; kcbv_in Q30; kcbv_in Q24; kcbv_in Q31; kcbv_in Q29. destr_conj KP. zimps.
          eapply (J700 R5 ci' B' H'). all: jfin.
      + zbr Rfd true.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J700 Rx ci B Hd) end. all: jfin. }
  clear KBA3 KLL KD J28.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (2 ^ lb + -1) ltac:(symmetry; rewrite mask_not_sllw by lia; lia).
  zstep Rfd.
  pose proof (land_mask_l' hold lb ltac:(lia)) as Ri0.
  pose proof (tab_root_entry LENS rdL lb na (Z.land (2 ^ lb + -1) hold) TOKL Ri0) as (Hbits0 & _ & _ & _).
  zstep Rfd.
  zsetreg (4 * Z.land (2 ^ lb + -1) hold) ltac:(symmetry; apply shiftl_2).
  zstep Rfd.
  tld4_bits HtL (Z.land (2 ^ lb + -1) hold).
  destruct (Z_lt_dec bits (code_bits (rdL (Z.land (2 ^ lb + -1) hold)))) as [Hneed | Hok].
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (l_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n la na lb (2 ^ lb + -1) cin bits cin bits hold fin rdL Hh) end.
    all: jfin.
    + intros R' H' G24 HH1' HH2' HB14 HBn KP. cbv [keptc KS_E1] in KP. kcbv_in G24. destr_conj KP. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' G28 G13 G14 G6 G24 G15 G18 X1 X2 X3 X4 X5 X6 X7 X8 KP. cbv [keptc KS_E1] in KP.
      kcbv_in G28; kcbv_in G13; kcbv_in G14; kcbv_in G6; kcbv_in G24; kcbv_in G15; kcbv_in G18. destr_conj KP. zimps.
      eapply (J40 R' ci' B' H'). all: jfin.
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J40 Rx cin bits hold) end. all: jfin.
Qed.
End FXG.
End S_Len.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.I9S Require Import SBase.
Import S_MatchL. Import S_Match. Import S_DistL. Import S_DistX. Import S_Dist. Import S_LenL. Import S_LenX. Import S_Len.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition L_FRET : Z := 91868.

End FXG.
Ltac st_cbn := cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

Definition st_fast (st : ist) (m ci co H B : Z) : ist :=
  IST m (t_last st) (t_flags st) ci co H B (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

Lemma sinv_after_fast : forall cx st lf cf m ci co H B,
  sinv cx st lf cf -> t_mode st = LEN ->
  0 <= ci -> ci <= c_n cx -> t_cout st <= co -> co <= c_osz cx ->
  0 <= B -> B <= 7 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  8 * (c_n cx - ci) + B + (c_osz cx - co) < 8 * (c_n cx - t_cin st) + t_bits st + (c_osz cx - t_cout st) ->
  8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
  (m = LEN \/ m = TYPE \/ m = BAD) ->
  sinv cx (st_fast st m ci co H B) lf cf /\ meas cx (st_fast st m ci co H B) < meas cx st.
Proof.
  intros cx st lf cf m ci co H B SI Hm Hci1 Hci2 Hco1 Hco2 HB1 HB2 HH1 HH2 HBc HW HI Hm'.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_fast, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN = HEAD \/ LEN = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  unfold RNG in R. icx_cbn. destr_conj R.
  dand P as (P1 & P2 & P3). unfold PROG, Wm in P1, P2, P3 |- *. icx_cbn.
  split; [split; [| split; [exact W | split]] |].
  - clear W Mf Mlive P1 P2 P3. unfold RNG. icx_cbn. split_conj; try assumption; lia_std.
  - clear W Mf Mlive Hm'. split; [lia_std | split; [lia_std |]].
    first [ exact P3 | destruct P3 as [E | [E C]]; [left; exact E | exfalso; clear - C; modes_cbv; lia_std] ].
  - unfold MODE. icx_cbn.
    split; [clear - Hm'; unfold reach; destruct Hm' as [-> | [-> | ->]]; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros HL; destruct Hm' as [-> | [-> | ->]];
              [ apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std
              | exfalso; clear - HL; unfold codes_liveP in HL; modes_cbv; lia_std ]
          | destruct Hm' as [-> | [-> | ->]]; mode_vacuous ].
  - clear - HW Hm'. pose proof (rank_range m) as RR. change (rank LEN) with 18. lia_std.
Qed.

Lemma win_arr : forall M w, 0 < w \/ w = 0 -> w + 32768 <= two64 -> (w <> 0 -> mem_wr R_segs M w 32768) ->
  exists fw, (w <> 0 -> mem_arr 1 R_segs M w 32768 fw) /\ (forall i, 0 <= i < 32768 -> 0 <= fw i < 256).
Proof.
  intros M w Hw Hw2 Ww. destruct (Z.eq_dec w 0) as [E|NE].
  - exists (fun _ => 0). split; [intros C; contradiction | intros; lia_std].
  - destruct (out_arr M w 32768 (Ww NE) ltac:(lia_std) ltac:(lia_std) Hw2) as (fw & A & B).
    exists fw. split; [intros _; exact A | exact B].
Qed.

Section LenF.
Hypothesis IFAST : ifast_spec_s.

Theorem len_s : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LEN -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes R_segs (zcfg R_segs L_LEN (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof SI as SI0. dand SI as (RNG_ & WIN_ & PROG_ & MODE_).
  pose proof KM as KM0. pose proof RG as RG0. open_kmem KM. open_std STD.
  assert (TLV : tables_live cx st cf).
  { assert (ML : codes_liveP (t_mode st) -> tables_live cx st cf) by mode_get MODE_.
    apply ML. rewrite Hmd. unfold codes_liveP. cbv [LEN_ LEN LIT]. lia. }
  dand (live_tabs cx st lf cf M CX RNG_ TLV ROM Hcodes) as (na & nd & TB). clear TLV MODE_ PROG_.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof CX as CX0. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold RNG in RNG_; icx_cbn; cbv [N_CODES N_LENS] in RNG_; destr_conj RNG_.
  unfold s_regs_d10, s_fix, s_vars in RG; icx_cbn; destr_conj RG.
  destruct SAT as [Hmode SREST]. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold tabsP in TB. icx_cbn. idtac.
  dand TB as (HtL & HtD & TOKL & TOKD & Cla1 & Cla2 & Cda1 & Cda2 & Cna & Cnd & ALla & ALda & Slaob & Slap & Sdaob & Sdap & Slap2 & Sdap2 & _).
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) lc) as la eqn:Ela.
  remember (cp_addr (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) dc) as da eqn:Eda.
  remember (rdc cf lc) as rdL eqn:ErdL. remember (rdc cf dc) as rdD eqn:ErdD. clear ErdL ErdD.
  pose proof (tab_ok_root _ _ _ _ TOKL) as (Hlb1 & Hna1 & _). pose proof (tab_ok_root _ _ _ _ TOKD) as (Hdb1 & Hnd1 & _).
  pose proof (pow2_15 lb ltac:(lia)) as HPlb. pose proof (pow2_15 db ltac:(lia)) as HPdb.
  prune_rng.
  zkeysb. unfold L_LEN, L_LSLOW, L_FRET, L_RELOAD, L_IFAST in *. cbv [JTAB_ADDR] in *.
  pose proof two64_eq as TW64.
  zstep Rfd.
  destruct (Z_lt_dec (n - cin) 6) as [Hh6 | Hh6].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec (osz - cout) 258) as [Hl258 | Hl258].
  { zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  (* 1.4: the fast path also needs bits < 8 (li a2,7; bltu a2,s8 -> the slow path) *)
  zstep Rfd.                          (* li a2,7 *)
  destruct (Z_lt_dec 7 bits) as [Hb8 | Hb8].
  { zbr Rfd true.                     (* bits >= 8: the slow path *)
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
      eapply (len_slow_s _ fin MD T M0 Rx lx M
                (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI0) end; [| exact KM0 | exact K].
    unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg. }
  zbr Rfd false.
  clear KM0 RG0.
  fp_frame_from HP0.
  pose proof K as KK. open_K KK. clear KD KD10 KD00 KSM KRA1 KB11 KB10 KBA3 KL KLL KRT.
  pose proof FRM as FR. unfold i_frame in FR. icx_cbn.
  dand FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S104 & S96 & _ & _ & _ & S72 & _).
  pose proof SOUT as S80. unfold s_out in S80. icx_cbn.
  pose proof CST as CS. unfold i_cst in CS. icx_cbn. dand CS as (S64u & _ & _ & _ & _ & _ & C60 & C72 & C7144).
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (C12 & C24 & C64 & C68 & C92 & C96 & C100 & C104 & C112 & C120 & C124 & C128 & C132 & C136 & C140 & C144).
  rewrite <- Ela in C104. rewrite <- Eda in C112. clear SREST.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    destruct (out_arr Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo);
    destruct (win_arr Mx w ltac:(lia) ltac:(rewrite TW64; lia) ltac:(intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X; exact X)) as (fw & Hwin & Rfw) end.
  pose proof WIN_ as WIN'. unfold WIN in WIN'. icx_cbn. cbv [WIN_SIZE] in WIN'. destruct WIN' as [WIN0 WIN1].
  unfold ifast_spec_s, ifast_spec_at in IFAST.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (IFAST Rx lx Mx MD T u p q n ob osz w whave wnext cin cout hold bits out lb db la na da nd (u + -224) 91868 135168 zc rdL rdD fin fo fw Hh) end.
  all: first [ lazymatch goal with
       | |- zget_l _ _ _ = _ => zreg
       | |- Z.land _ _ = _ => reflexivity
       | |- ZSEP _ => first [ assumption | exact (sep_ob_u _ _ SEP) | exact (sep_p_ob _ _ SEP) | exact (sep_p_q _ _ SEP) | exact (sep_ob_q _ _ SEP)
                            | exact (sep_w_p _ _ SEP) | exact (sep_w_q _ _ SEP) | exact (sep_w_ob _ _ SEP) ]
       | |- tab_ok _ _ _ _ = true => assumption
       | |- _ mod _ = _ => first [ assumption | exact (proj1 AL) | exact (proj1 (proj2 AL))
                                 | pose proof (proj1 AL) as ALu; clear - ALu; cbn in ALu; Z.to_euclidean_division_equations; lia ]
       | |- _ \/ _ => destruct (Z.eq_dec w 0) as [Ew|Nw]; [left; exact Ew | right; split; [lia | split; [cbv [WIN_SIZE ]; lia | exact (proj2 (proj2 AL))]]]
       | |- _ -> mem_wr _ _ _ _ => intros Hw; pose proof Ww as X; rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw) in X; cbv [WIN_SIZE] in X |- *; exact X
       | |- _ -> mem_arr _ _ _ _ _ _ => exact Hwin
       | |- _ -> _ /\ _ => first [exact WIN0 | cbv [WIN_SIZE]; exact WIN1]
       | |- mem_wr _ _ _ _ => first [assumption | exact Wstk]
       | |- mem_arr _ _ _ _ _ _ => assumption
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => first [assumption | exact C60 | cbv [LEN]; assumption]
       | |- forall i : Z, _ => first [exact Hfin | exact Rfo | exact Rfw]
       | |- forall R' M', _ => idtac
       | |- _ => cbv [FRA STATE_SIZE WIN_SIZE FR_IF FR_INF]; first [assumption | lia]
       end | match goal with |- ?G => idtac "IFAIL" G end ].
  intros R' M' cin' cout' hold' bits' mode' fo' Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3 HWlt HIle Hm' HP E8 E16 E32 E40 P80 P88 P8 HOB' Rfo' KE.
  unfold kept_eq in KE. zkeys. destr_conj KE. zimps.
  clear Hmode HOB Hwin C60 C72 C7144 S64u HtL HtD.
  repeat match goal with
         | H : mem_u64 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u64 _ _ (u) _ => clear H | mem_u64 _ _ (u + 24) _ => clear H | mem_u64 _ _ (p + 96) _ => clear H end end
         | H : mem_u32 _ ?Mo _ _ |- _ => lazymatch Mo with M' => fail | _ => lazymatch type of H with
             | mem_u32 _ _ (u + 8) _ => clear H | mem_u32 _ _ (u + 32) _ => clear H | mem_u32 _ _ (p + 104) _ => clear H end end
         end.
  unfold if_fp in HP. cbv [FR_IF] in HP. zreattachL HP.
  assert (Hmv : 0 <= mode' < 2147483648) by (clear - Hm'; cbv [LEN TYPE BAD] in Hm'; lia).
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zstep Rfd.
  tstep1 Rfd.
  unfold KRELOAD in KRL. zkeys.
  assert (JRA : forall R9 M9 (m9 : Z),
    (m9 = LEN \/ m9 = TYPE \/ m9 = BAD) -> m9 = mode' \/ (m9 = TYPE /\ mode' = TYPE) ->
    zget R9 3 = u + -224 -> zget R9 4 = K0 4%positive -> zget R9 5 = K0 5%positive -> zget R9 9 = p -> zget R9 11 = u ->
    zget R9 12 = 0 -> zget R9 21 = 16209 -> zget R9 23 = p + 168 -> zget R9 26 = 67008 ->
    zget R9 27 = q + cin' -> zget R9 19 = n - cin' -> zget R9 20 = ob + cout' -> zget R9 2 = osz - cout' ->
    zget R9 24 = hold' -> zget R9 25 = bits' ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M9 -> mem_u32 R_segs M9 (p + 8) m9 ->
    st_rest R_segs (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) M9 ->
    mem_arr 2 R_segs M9 (p + 168) 320 lf -> mem_arr 4 R_segs M9 (p + 1384) 1444 cf ->
    framed (fun X => mpostL R_segs M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M9 ->
    realizes R_segs (zcfg R_segs 91732 (zupd R9 []) M9 MD) T).
  { intros R9 M9 m9 Hm9 _ G3 G4 G5 G26 G11 G12 G20 G22 G25 G28 G10 G19 G2 G23 G24 STD9 Hmo9 SR9 RET9 OUT9 HL9 HC9 HAG9.
    pose proof (sinv_after_fast _ _ lf cf m9 cin' cout' hold' bits' SI0 eq_refl Hci1 Hci2 Hco1 Hco2 Hb1 Hb2 Hho1 Hho2 Hb3
                  ltac:(cbn; lia) ltac:(cbn; lia) Hm9) as [SI9 ME9].
    unfold st_fast in SI9, ME9. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI9, ME9.
    eapply (KRL R9 M9 _ lf cf SI9 ME9).
    - unfold s_regs_reload; icx_cbn; zkeys; split_conj; try assumption; first [intros C; discriminate C | intros _; assumption].
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption. all: exact SR9. }
  destruct (Z.eq_dec mode' TYPE) as [HmT | HmT]; cbv [TYPE] in HmT.
  - zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
  - zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JRA Rx Mx mode' Hm' ltac:(left; reflexivity)) end.
    all: try zreg.
    all: first [close_std | assumption | unfold st_rest; icx_cbn; split_conj; first [assumption | subst la; assumption | subst da; assumption]].
Qed.

Theorem arm_LEN : arm_stmt L_LEN LEN.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply len_s; try eassumption.
Qed.

Lemma sinv_len_ : forall cx st lf cf,
  sinv cx st lf cf -> t_mode st = LEN_ ->
  sinv cx (st_le st LEN (t_length st) (t_extra st)) lf cf /\ meas cx (st_le st LEN (t_length st) (t_extra st)) < meas cx st.
Proof.
  intros cx st lf cf SI Hm.
  dand SI as (R & W & P & Mo).
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold sinv, st_le, meas, Wm in *. icx_cbn. subst mode.
  assert (Mf : flags = -1 -> (LEN_ = HEAD \/ LEN_ = BAD) /\ cout = 0) by mode_get Mo.
  assert (Mlive : codes_liveP LEN_ -> tables_live (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
            (IST LEN_ last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cf) by mode_get Mo.
  clear Mo.
  split; [split; [exact R | split; [exact W | split; [prog_transfer P|]]] |].
  - unfold MODE. icx_cbn.
    split; [clear; unfold reach; modes_cbv; lia_std |].
    split; [intros E; destruct (Mf E) as [HM _]; exfalso; clear - HM; modes_cbv; lia_std |].
    split_conj;
    first [ intros _; apply Mlive; clear; unfold codes_liveP; modes_cbv; lia_std
          | mode_vacuous ].
  - clear. cbv [rank]. modes_cbv. cbn. lia_std.
Qed.

Theorem arm_LEN_ : arm_stmt L_LEN_ LEN_.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof (sinv_len_ cx st lf cf SI Hmd) as [SI1 ME1].
  open_kmem KM. destruct SAT as [Hmode SREST].
  dand RG as (FIX & VARS & G27).
  pose proof CX as CX0. destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  repeat match goal with H : 0 <= K0 _ |- _ => clear H | H : K0 _ < _ |- _ => clear H | H : 0 <= K0 _ < _ |- _ => clear H end.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn. subst mode.
  unfold s_fix, s_vars in FIX, VARS. icx_cbn. destr_conj FIX. destr_conj VARS.
  open_std STD. icx_cbn. cbv [N_LENS N_CODES] in Hlens, Hcodes.
  unfold st_le in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
  zkeysb. unfold L_LEN_, L_LEN in *. cbv [JTAB_ADDR] in *. pose proof two64_eq as TW64.
  fp_frame_from HP0.
  zstep Rfd.
  clear Hmode.
  tstep1 Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
    eapply (len_s _ fin MD T M0 Rx lx Mx
              (IST LEN last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
              lf cf CX0 Hh Hfin eq_refl SI1) end.
  - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
  - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
    all: first [cbv [LEN]; assumption | exact SREST | exact SRET | exact SOUT | exact HAG].
  - eapply KALL_mono; [| exact K]. clear - ME1. lia.
Qed.
End LenF.
End FXG.
