(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require Import SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_MLOOP : Z := 93172.
Definition L_MAFTER : Z := 93196.
Definition L_SETLEN : Z := 93212.

Ltac modes_cbv := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.
Ltac mode_get Mo := clear - Mo; unfold MODE in Mo; icx_cbn;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; assumption.
Ltac mode_vacuous := let HE := fresh "HE" in intros HE; exfalso;
  repeat match goal with H : _ |- _ => lazymatch H with HE => fail | _ => clear H end end;
  unfold codes_liveP in *; modes_cbv; lia_std.

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

Lemma mem_u32_u8 {RCa1 : RunCtx}  : forall M a v, mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a v.
Proof.
  intros M a v H. unfold mem_u32, mem_u8, mem_is in *.
  pose proof (mem_is_firstn (run_segments R_segs rc_inp rc_sp rc_mb) M a (Z_to_le_bytes 4 v) 1 H ltac:(cbn; lia_std)) as H1.
  cbn [firstn Z_to_le_bytes] in H1. exact H1.
Qed.


Lemma zfupd_byte : forall (f : Z -> Z) i v lo hi,
  (forall j, lo <= j < hi -> 0 <= f j < 256) -> 0 <= v < 256 -> forall j, lo <= j < hi -> 0 <= zfupd f i v j < 256.
Proof. intros f i v lo hi Hf Hv j Hj. unfold zfupd. destruct (Z.eqb_spec j i); [lia_std | apply Hf; lia_std]. Qed.

Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.

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

Lemma mloop_w {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz w wn si c m : Z) (fo fw : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = w + si -> zget_l Rb l kS3 = ob + c -> zget_l Rb l kA4 = w + si + m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= si -> si + m <= wn -> 0 <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 -> 0 < w -> w + wn <= 140737488355328 -> ZSEP (w + wn <= ob \/ ob + osz <= w) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M w wn fw -> (forall i, 0 <= i < wn -> 0 <= fw i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA3 = w + si + m -> zget R' kS3 = ob + c + m ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kRA = zget_l Rb l kRA -> zget R' kT6 = zget_l Rb l kT6 -> zget R' kT4 = zget_l Rb l kT4 ->
     zget R' kS9 = zget_l Rb l kS9 -> zget R' kS4 = zget_l Rb l kS4 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS8 = zget_l Rb l kS8 ->
     zget R' kS11 = zget_l Rb l kS11 -> zget R' kA2 = zget_l Rb l kA2 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' w wn fw -> P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP (zupd Rb l) M MD) T.
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

Lemma mloop_o {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz s c m : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA3 = ob + s -> zget_l Rb l kS3 = ob + c -> zget_l Rb l kA4 = ob + s + m ->
  1 <= m -> m <= Z.of_nat N -> 0 <= s -> s <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     zget R' kA3 = ob + s + m -> zget R' kS3 = ob + c + m ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kA0 = zget_l Rb l kA0 -> zget R' kA1 = zget_l Rb l kA1 ->
     zget R' kRA = zget_l Rb l kRA -> zget R' kT6 = zget_l Rb l kT6 -> zget R' kT4 = zget_l Rb l kT4 ->
     zget R' kS9 = zget_l Rb l kS9 -> zget R' kS4 = zget_l Rb l kS4 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS8 = zget_l Rb l kS8 ->
     zget R' kS11 = zget_l Rb l kS11 -> zget R' kA2 = zget_l Rb l kA2 ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP (zupd Rb l) M MD) T.
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

Definition PM {RCa1 : RunCtx}  (cx : ictx) (fin : Z -> Z) (M0 : mem) (md : Z) (st : ist) (lf cf : Z -> Z) (M : mem) : Prop :=
  s_std cx fin M /\ mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 8) md /\ st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ s_ret cx st M /\ s_out cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf /\
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_loop cx).

Lemma PM_store {RCa1 : RunCtx}  : forall cx fin M0 md st lf cf M a v,
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

Lemma out_arr {RCa1 : RunCtx}  : forall M ob osz, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> 0 <= ob -> 0 <= osz -> ob + osz <= two64 ->
  exists fo, mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).
Proof.
  intros M ob osz W H1 H2 H3. destruct (mem_wr_arr_exists_R M ob osz W H1 H2 H3) as [fo [A B]].
  exists fo. split; [exact A | intros i _; apply B].
Qed.

