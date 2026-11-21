(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_MatchL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's THREE OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Notation L_MLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_MLOOP (only parsing).
Notation L_MAFTER := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_MAFTER (only parsing).
Notation L_SETLEN := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_SETLEN (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholdsv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).

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
                    | clear H ]
          end;
          zmem_post
      end
  end.

(* OPENERS OF THE LIST FORM (they only unfold, split and name): a list-form hypothesis: the meaning over the
   layout's list is unfolded, the conjunction split and its parts named; the same for a goal *)
Ltac open_lists :=
  repeat match goal with
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mloop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mafter] in HL;
             destr_conj HL
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_mloop] in HL; destr_conj HL
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mloop
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mafter OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_mloop];
  split_conj.

Lemma mloop_w {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz w wn si c m : Z) (fo fw : Z -> Z),
  m_halted MD = None ->
  rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mloop [w + si; ob + c; w + si + m] ->
  1 <= m -> m <= Z.of_nat N -> 0 <= si -> si + m <= wn -> 0 <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 -> 0 < w -> w + wn <= 140737488355328 -> ZSEP (w + wn <= ob \/ ob + osz <= w) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M w wn fw -> (forall i, 0 <= i < wn -> 0 <= fw i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mafter [w + si + m; ob + c + m] ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_mloop ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' w wn fw -> P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz w wn si c m fo fw Hh RH Hm1 Hm2 Hsi1 Hsi2 Hc1 Hc2
    Hob1 Hob2 Hw1 Hw2 Swob Wob HOB Rfo Hwin Rfw HP HPres K; [lia|].
  open_lists.
  zkeys. unfold L_MLOOP, L_MAFTER in *. pose proof two64_eq as TW64.
  pose proof (Rfw si ltac:(lia)) as Rb0.
  (* ONE RUN to the store of the copied byte: the run stops where this text's array-store word applies *)
  zuntil Rfd (idtac; tstore_arrP Rfd HOB c HP HPres).
  (* ONE RUN to the loop's exit test *)
  zto_branch_q Rfd.
  pose proof (zfupd_byte fo c (fw si) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - (* the last byte: ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fw si))) end);
      [ split_lists | split_lists | .. ]; try zreg; try assumption.
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz w wn (si + 1) (c + 1) (m - 1) (zfupd fo c (fw si)) fw Hh) end);
      [ split_lists | .. ]; try zreg; try assumption; try lia.
    (* the inner continuation gives the outer one: the same place, the model values re-said *)
    intros R' M' fo' RH' KP' Wob' HOB' Rfo' Hwin' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
      first [ assumption | (etransitivity; [ eassumption | lia ]) ].
Qed.

Lemma mloop_o {RCa1 : RunCtx}  : forall (N : nat) (P : mem -> Prop) Rb l M MD T (ob osz s c m : Z) (fo : Z -> Z),
  m_halted MD = None ->
  rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mloop [ob + s; ob + c; ob + s + m] ->
  1 <= m -> m <= Z.of_nat N -> 0 <= s -> s <= c -> c + m <= osz ->
  0 <= ob -> ob + osz <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  P M -> (forall M' a v, P M' -> ob <= a -> a + 1 <= ob + osz -> P (wbytes M' (w64 a) (Z_to_le_bytes 1 v))) ->
  (forall R' M' (fo' : Z -> Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_mafter [ob + s + m; ob + c + m] ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_mloop ->
     mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' ob osz fo' -> (forall i, 0 <= i < osz -> 0 <= fo' i < 256) ->
     P M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MLOOP (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros P Rb l M MD T ob osz s c m fo Hh RH Hm1 Hm2 Hs1 Hs2 Hc2
    Hob1 Hob2 Wob HOB Rfo HP HPres K; [lia|].
  open_lists.
  zkeys. unfold L_MLOOP, L_MAFTER in *. pose proof two64_eq as TW64.
  pose proof (Rfo s ltac:(lia)) as Rb0.
  (* ONE RUN to the store of the copied byte: the run stops where this text's array-store word applies *)
  zuntil Rfd (idtac; tstore_arrP Rfd HOB c HP HPres).
  (* ONE RUN to the loop's exit test *)
  zto_branch_q Rfd.
  pose proof (zfupd_byte fo c (fo s) 0 osz Rfo Rb0) as Rfo1.
  destruct (Z.eq_dec m 1) as [E1|N1].
  - (* the last byte: ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (K Rx Mx (zfupd fo c (fo s))) end);
      [ split_lists | split_lists | .. ]; try zreg; try assumption.
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH P Rx lx Mx MD T ob osz (s + 1) (c + 1) (m - 1) (zfupd fo c (fo s)) Hh) end);
      [ split_lists | .. ]; try zreg; try assumption; try lia.
    (* the inner continuation gives the outer one: the same place, the model values re-said *)
    intros R' M' fo' RH' KP' Wob' HOB' Rfo' HP'.
    eapply (K R' M' fo'); try assumption; try lia.
    open_lists; zgetl_nil; split_lists; cbv beta iota delta [zget_l alookup];
      first [ assumption | (etransitivity; [ eassumption | lia ]) ].
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
  split_conj; try assumption; try close_std; try exact HAG; try exact I.
Qed.

Lemma out_arr {RCa1 : RunCtx}  : forall M ob osz, mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz -> 0 <= ob -> 0 <= osz -> ob + osz <= two64 ->
  exists fo, mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).
Proof.
  intros M ob osz W H1 H2 H3. destruct (mem_wr_arr_exists_R M ob osz W H1 H2 H3) as [fo [A B]].
  exists fo. split; [exact A | intros i _; apply B].
Qed.

End S_MatchL.

Module S_Match.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's FOUR OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Notation L_M4C := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_M4C (only parsing).
Notation L_M54 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_M54 (only parsing).
Notation L_M30 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_M30 (only parsing).
Notation L_M3C := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_M3C (only parsing).

(* THE MODULE's REGISTER MAP: which register holds which of the values that the definition binds is the layout's
   list; the values, in the list's order of numbering: the stream's address, the two entry values, the state's
   address, the input left, the output room left, the bit accumulator, its bit count, the next input address, the
   next output address after `dput` bytes, the output count at the pass's entry *)
Definition m_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout hold bits out dput : Z) (R : tree Z) : Prop :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [u; K0 kGP; K0 kTP; p; n - cin; osz - cout; hold; bits; q + cin; ob + cout + dput; out])
    R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_m.
Ltac open_mregs H :=
  unfold m_regs in H;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_m JTAB_ADDR] in H;
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in H;
  destr_conj H; zgetl_nil.
Ltac close_mregs :=
  unfold m_regs;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_m JTAB_ADDR];
  split_conj; zreg.

Theorem match_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = MATCH -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MATCH (zupd Rb l) M MD) T.
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
  { unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    (* no room left: ONE RUN to the leave place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end).
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - first [ exact SOUT | exact I ].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  clear KLL.
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
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_MAFTER (zupd R' []) M' MD) T).
  { intros R' M' copy MR G13 Hc1 Hc2 Hc3 HPM. open_mregs MR. cbv [kA2] in G13.
    unfold L_MAFTER.
    dand HPM as (STD' & Hm' & SR' & RET' & OUT' & HL' & HC' & HP0'). unfold st_upd in SR', RET', OUT'. icx_cbn.
    pose proof SR' as SR2. unfold st_rest in SR2. icx_cbn. dand SR2 as (_ & _ & _ & _ & C92' & _).
    (* ONE RUN to the test of the length that is left *)
    zto_branch_q Rfd.
    unfold KSETMODE, L_SETMODE in KSM. unfold KDISP10, L_DISP10 in KD10. zkeys.
    destruct (Z.eq_dec (length - copy) 0) as [E0 | N0].
    + (* nothing left: ONE RUN to the mode's set place *)
      pose proof (sinv_upd _ _ lf cf LEN copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ MATCH lf cf SI1 ME1) end).
      * unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
      * exact STD'.
      * exact Hm'.
      * exact SR'.
      * exact RET'.
      * exact OUT'.
      * exact HL'.
      * exact HC'.
      * exact HP0'.
    + (* more to copy: ONE RUN to the dispatch place *)
      pose proof (sinv_upd _ _ lf cf MATCH copy (length - copy) SI0 ltac:(left; reflexivity) Hc1 Hc3 ltac:(lia) ltac:(cbn [t_length]; lia)
                    ltac:(left; split; [reflexivity | split; [reflexivity | lia]])) as [SI1 ME1].
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KD10 Rx Mx _ lf cf SI1 ME1) end).
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
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_M54 (zupd R2 []) M MD) T).
  { intros R2 copy src MR Q13 Q15 Hk1 Hk2 Hk3 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in Q13, Q15, HSRC.
    unfold L_M54.
    clear C60 C72 C7144 S72 S80.
    assert (Q14 : exists from, zget R2 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : match src with inl so => from = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => from = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (destruct src; rewrite <- Q14; exact HSRC).
    clear HSRC.
    (* the state's closed relation is cleared before the run that writes one of its fields; the output array's
       fact and the count's zero-extension fact are stated before the run *)
    clear SREST.
    destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
    pose proof (zext32_shift (copy + -1) ltac:(lia)) as ZX.
    destruct src as [so | si].
    - dand HS2 as (Hfrom & Hso1 & Hso2). subst from.
      (* ONE RUN to the copy loop's head (the copy from the output) *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_o (Z.to_nat copy)
                  (PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
                      (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              MATCH copy (length - copy)) lf cf)
                  Rx lx Mx MD T ob osz so cout copy fo Hh) end).
      1: split_lists.
      all: try zreg. all: try lia. all: try assumption.
      { unfold PM, st_upd, s_ret, s_out, st_rest; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; first [exact I | exact HAG]. }
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 RH9 KP9 Wob9 HOB9 Rfo9 HPM9.
      open_lists. zgetl_nil.
      zimps.
      eapply (JA R9 M9 copy); try exact HPM9; try lia; [close_mregs | zreg].
    - dand HS2 as (Hfrom & Hsi1 & Hsi2 & Hw0). subst from.
      pose proof Ww as Ww32. rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in Ww32. cbv [WIN_SIZE] in Ww32.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        destruct (out_arr Mx w 32768 Ww32 ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fw & HWA & Rfw) end.
      pose proof (sep_w_ob ROMHI_S _ SEP) as SWO. icx_cbn. cbv [WIN_SIZE] in SWO.
      assert (SWO' : ZSEP (w + 32768 <= ob \/ ob + osz <= w)) by (unfold ZSEP; clear - SWO Hw0; lia). clear SWO.
      (* ONE RUN to the copy loop's head (the copy from the window) *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
        eapply (mloop_w (Z.to_nat copy)
                  (PM (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0 MATCH
                      (st_upd (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                              MATCH copy (length - copy)) lf cf)
                  Rx lx Mx MD T ob osz w 32768 si cout copy fo fw Hh) end).
      1: split_lists.
      all: try zreg. all: try lia. all: try assumption.
      { unfold PM, st_upd, s_ret, s_out, st_rest; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; first [exact I | exact HAG]. }
      { intros MX a v HX Ha1 Ha2. exact (PM_store _ fin M0 MATCH _ lf cf MX a v CX0 HX Ha1 Ha2). }
      intros R9 M9 fo9 RH9 KP9 Wob9 HOB9 Rfo9 Hwin9 HPM9.
      open_lists. zgetl_nil.
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
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_M4C (zupd R' []) M MD) T).
  { intros R' copy0 src MR G13 G15 Hc1 Hc2 HSRC. open_mregs MR. cbv [kA2 kA4 kA3] in G13, G15, HSRC.
    unfold L_M4C.
    assert (Q14 : exists from, zget R' 14 = from) by (eexists; reflexivity). destruct Q14 as [from Q14].
    assert (HS2 : forall copy, copy <= copy0 -> match src with inl so => zget R' 14 = ob + so /\ 0 <= so /\ so <= cout
                                | inr si => zget R' 14 = w + si /\ 0 <= si /\ si + copy <= 32768 /\ w <> 0 end)
      by (intros copy Hcp; destruct src; [exact HSRC | dand HSRC as (X1 & X2 & X3 & X4); repeat split; try assumption; lia]).
    assert (G14 : zget R' 14 = from) by exact Q14.
    clear HSRC Q14.
    destruct (Z_lt_dec copy0 (osz - cout)) as [Hlt | Hge].
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx copy0 src) end); try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 copy0 ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end.
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J54 Rx (osz - cout) src) end); try zreg; try lia; try close_mregs.
      cbv [kA3]. pose proof (HS2 (osz - cout) ltac:(lia)) as X. destruct src;
        lazymatch goal with |- ?a = _ /\ ?rest => replace a with from by (symmetry; zreg); rewrite <- G14; exact X end. }
  clear J54.
  (* ONE RUN to the test of the distance against the output written *)
  zto_branch_q Rfd.
  destruct (Z_lt_dec (cout - cout0) offset) as [Hwin | Hout].
  2: {
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx length (inl (cout - offset))) end); try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  (* ONE RUN to the test of the distance against the window's fill *)
  zto_branch_q Rfd.
  destruct (Z_lt_dec whave (offset - (cout - cout0))) as [Hfar | Hok].
  {
    unfold KBADMSG_S10, L_BADMSG_S10 in KB10.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
      eapply (KB10 Rx Mx (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end).
    - apply sinv_bad_of. exact SI0.
    - pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST MATCH last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB.
      cbn [t_mode] in MB. change (rank MATCH) with 14 in MB. clear - MB. lia.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - cbv [kA2]. rewrite TW64. zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std; try exact HAG; try exact I. }
  assert (Hw0 : w <> 0) by (intros E; destruct (WIN0 E); lia).
  dand (WIN1 Hw0) as (Wh1 & Wn1 & Whn). clear WIN0 WIN1.
  rewrite (wsz_some (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) Hw0) in C60. cbv [WIN_SIZE] in C60.
  assert (J3C : forall R' (copy0 si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = copy0 -> zget R' kA3 = si -> zget R' kA4 = length ->
    1 <= copy0 -> copy0 <= length -> 0 <= si -> si + copy0 <= 32768 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_M3C (zupd R' []) M MD) T).
  { intros R' copy0 si MR G13 G14 G15 Hc1 Hc2 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3 kA4] in G13, G14, G15.
    unfold L_M3C.
    (* the index's zero-extension equation is stated before the run *)
    pose proof (zext32_shift si ltac:(lia)) as ZX.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J4C Rx copy0 (inr si)) end); try zreg; try lia; try close_mregs.
    all: cbv [kA3]; split; [zreg | lia]. }
  assert (J30 : forall R' (cp si : Z),
    m_regs u p q n ob osz K0 cin cout hold bits out 0 R' ->
    zget R' kA2 = cp -> zget R' kA3 = si ->
    1 <= cp -> cp < 98304 -> 0 <= si -> si + cp <= 32768 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_M30 (zupd R' []) M MD) T).
  { intros R' cp si MR G13 G14 Hc1 Hc98 Hsi1 Hsi2. open_mregs MR. cbv [kA2 kA3] in G13, G14.
    unfold L_M30.
    zto_branch_q Rfd.
    destruct (Z_lt_dec cp length) as [Hlt | Hge].
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx cp si) end); try zreg; try lia; close_mregs.
    - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J3C Rx length si) end); try zreg; try lia; close_mregs. }
  clear J3C J4C.
  (* ONE RUN to the test of the distance against the window's write place *)
  zto_branch_q Rfd.
  destruct (Z_lt_dec wnext (offset - (cout - cout0))) as [Hwrap | Hlin].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0) - wnext) (32768 - (offset - (cout - cout0) - wnext))) end); try zreg; try lia; close_mregs.
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J30 Rx (offset - (cout - cout0)) (wnext - (offset - (cout - cout0)))) end); try zreg; try lia; close_mregs.
Qed.

Theorem lit_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LIT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LIT (zupd Rb l) M MD) T.
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
  { unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
    (* no room left: ONE RUN to the leave place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KLL Rx Mx _ lf cf SI0) end).
    - unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - exact SRET.
    - first [ exact SOUT | exact I ].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  clear KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn.
  dand SR0 as (_ & _ & _ & _ & C92 & _).
  pose proof (mem_u32_u8 _ _ _ C92) as B92.
  destruct (out_arr _ ob osz Wob ltac:(lia) ltac:(lia) ltac:(rewrite TW64; lia)) as (fo & HOB & Rfo).
  (* ONE RUN to the store of the literal byte: the run stops where the kit's array-store word applies *)
  zuntil Rfd (idtac; tstore_arr Rfd HOB (cout)).
  unfold KSETMODE, L_SETMODE in KSM. zkeys.
  pose proof (sinv_upd _ _ lf cf LEN 1 length SI0 ltac:(right; reflexivity) ltac:(lia) ltac:(cbn [c_osz t_cout]; lia) ltac:(lia) ltac:(cbn [t_length]; lia) ltac:(right; reflexivity)) as [SI1 ME1].
  (* ONE RUN to the mode's set place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (KSM Rx Mx _ LIT lf cf SI1 ME1) end).
  - unfold s_regs_d0, s_fix, s_vars, st_upd; icx_cbn; zkeys; cbv [JTAB_ADDR LEN]; split_conj; zreg.
  - close_std.
  - exact Hmode.
  - unfold st_upd; icx_cbn. exact SREST.
  - exact SRET.
  - first [ exact SOUT | exact I ].
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_MATCH {RCa1 : RunCtx}  : arm_stmt L_MATCH MATCH.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply match_s; try eassumption.
Qed.

Theorem arm_LIT {RCa1 : RunCtx}  : arm_stmt L_LIT LIT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply lit_s; try eassumption.
Qed.
End S_Match.

Module S_DistL.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's ELEVEN OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Notation L_DLOOP1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DLOOP1 (only parsing).
Notation L_D04 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_D04 (only parsing).
Notation L_DLOOP2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DLOOP2 (only parsing).
Notation L_D8BC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_D8BC (only parsing).
Notation L_DXLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DXLOOP (only parsing).
Notation L_DX80 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DX80 (only parsing).
Notation L_LXLOOP := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LXLOOP (only parsing).
Notation L_LX60 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LX60 (only parsing).
Notation L_LVX_L1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LVX_L1 (only parsing).
Notation L_LVX_L2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LVX_L2 (only parsing).
Notation L_LVX_EXT := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_LVX_EXT (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholdsv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv (only parsing).
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

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

(* THREE SMALL HINT LEMMAS (new in the run form). Each is an equation that the hand text proved at its place for
   one value; here it is said once, with the left side in the form the run meets. A run's hint names it. *)
Lemma shl2_mul4 : forall x, Z.shiftl x 2 = 4 * x.
Proof. intros x. exact (shiftl_2 x). Qed.
Lemma zext32_shr30 : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
Proof. intros x Hx. exact (zext32_shift30 x Hx). Qed.
Lemma div_add_comm : forall a d v, a / 2 ^ d + v = v + a / 2 ^ d.
Proof. intros. apply Z.add_comm. Qed.


Ltac tld4_op Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_op (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_bits Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr4_bits (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld4_val Ha i :=
  lazymatch type of Ha with mem_arr 4 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lhu_arr4_val (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | ]); znorm end.
Ltac tld1 Ha i Hr :=
  lazymatch type of Ha with mem_arr 1 _ _ ?base ?n ?f =>
  let pc := zpc in
  Rfd pc ltac:(fun F E D => eapply (zu_lbu_arr' (run_segments R_segs rc_inp rc_sp rc_mb) _ _ _ _ _ _ _ _ _ _ base n f i);
     [exact F | exact E | exact D | zhalted | exact Ha | znorm; lia | lia | apply Hr; lia | ]); znorm end.
Ltac zlastval := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?x) :: _)) _ _) _ => x end.

Fixpoint keptc (Rb : tree Z) (l : list (positive * Z)) (R' : tree Z) (ks : list positive) : Prop :=
  match ks with
  | [] => True
  | k :: ks' => zget R' k = zget_l Rb l k /\ keptc Rb l R' ks'
  end.
(* THE FIVE LISTS OF REGISTERS THAT A LOOP OR A STUB LEAVES ALONE ARE FIELDS OF THE LAYOUT TEXT; here they have the
   hand text's short names (local to this module) *)
Local Notation KS_D1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d1 (only parsing).
Local Notation KS_D2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d2 (only parsing).
Local Notation KS_X := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_x (only parsing).
Local Notation KS_L1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l1 (only parsing).
Local Notation KS_L2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l2 (only parsing).

(* the closing words of a keep list: the list is unfolded with the register keys, split, and each part closed *)
Ltac keptc_keys :=
  cbv [keptc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_x
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l2
       kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6].
Ltac keptc_close := keptc_keys; split_conj; try exact I; zreg.
Ltac keptc_open HK :=
  cbv [keptc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_x
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l2
       kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in HK;
  destr_conj HK.
Ltac keptc_chain HK :=
  cbv [keptc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_x
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_lenf_l2
       kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in HK |- *;
  destr_conj HK; split_conj; try exact I;
  cbv [zget_l] in *; cbn [alookup Pos.eqb] in *; first [assumption | reflexivity].

(* OPENERS OF THE LIST FORM (they only unfold, split and name): a list-form hypothesis: the meaning over the
   layout's list is unfolded, the conjunction split and its parts named; the same for a goal *)
Ltac open_lists3 :=
  repeat match goal with
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k] in HL;
             destr_conj HL
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_l1] in HL;
             destr_conj HL
         end.
Ltac split_lists3 :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_l1];
  split_conj.

Lemma d_loop1 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db dm c0 b0 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1
    [da; dm; n - ci; q + ci; B; B; H; code_bits (rdD (Z.land dm H)); da + 4 * Z.land dm H; n - c0; b0; q + c0] ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < code_bits (rdD (Z.land dm H)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  dm = 2 ^ db - 1 -> 1 <= db -> db <= 15 -> 2 ^ db <= nd -> tab_ok DISTS rdD db nd = true ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (forall R' (H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x [H'] ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_D1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
       [q + ci'; n - ci'; B'; B'; H'; code_bits (rdD (Z.land dm H')); da + 4 * Z.land dm H'] ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> B' <= 22 -> code_bits (rdD (Z.land dm H')) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D1 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D04 (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP1 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db dm c0 b0 ci B H fin rdD Hh RH
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hdm Hdb1 Hdb2 Hnd TOK Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  open_lists3.
  zkeys. unfold L_DLOOP1, L_D04, L_LVX_L1 in *. pose proof two64_eq as TW64.
  pose proof (pow2_15 db ltac:(lia)) as HPdb.
  pose proof (land_mask_l H db ltac:(lia)) as Ri0. rewrite <- Hdm in Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm H) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits0 & _ & _ & _).
  assert (HB14 : B <= 14) by lia.
  pose proof (pow2_48 B ltac:(lia)) as HPB.
  destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz].
  { (* no input left: ONE RUN to the leave stub *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end);
      [ split_lists3 | .. ]; try zreg; try lia.
    - replace (b0 + 8 * (n - c0)) with B by lia. lia.
    - keptc_close. }
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  (* THE PULLED BYTE's VALUE EQUATION is stated before the run (no hint for it); the model's facts of the new
     accumulator value are said before the run too, at the value as the run leaves it *)
  pose proof (shl_byte (fin ci) B ltac:(lia) ltac:(lia)) as E1.
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (land_mask_l (Z.shiftl (fin ci) (B mod 64) + H) db ltac:(lia)) as Ri1. rewrite <- Hdm in Ri1.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land dm (Z.shiftl (fin ci) (B mod 64) + H)) TOK ltac:(rewrite Hdm; apply land_mask_l; lia)) as (Hbits1 & _ & _ & _).
  (* ONE RUN through the loop's body to its exit test, with ONE VALUE HINT (the table index, scaled: the table
     load's address must be read) *)
  zto_branch_hq Rfd (first [ zhint shl2_mul4 ]).
  set (H' := Z.shiftl (fin ci) (B mod 64) + H) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (subst H'; rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1 E1.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (code_bits (rdD (Z.land dm H')))) as [Hmore | Hdone].
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db dm c0 b0 (ci + 1) (B + 8) H' fin rdD Hh) end);
      [ split_lists3 | .. ]; try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' RH' X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - (* enough bits: ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end);
      [ split_lists3 | .. ]; try zreg; try lia.
    all: keptc_close.
Qed.

Lemma d_loop2 {RCa1 : RunCtx}  : forall (N : nat) Rb l M MD T (q n da nd db lo v m2 c1 b1 ci B H : Z) (fin rdD : Z -> Z),
  m_halted MD = None ->
  rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2
    [m2; db; v; da; n - c1; b1; q + c1; n - ci; q + ci; B; B; H;
     da + 4 * (v + Z.land H m2 / 2 ^ db); code_bits (rdD (v + Z.land H m2 / 2 ^ db))] ->
  n - ci < Z.of_nat N -> 0 <= c1 -> c1 <= ci -> ci <= n -> 0 <= b1 -> B = b1 + 8 * (ci - c1) ->
  B < db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)) -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  m2 = 2 ^ (db + lo) - 1 -> 1 <= db -> db <= 15 -> 1 <= lo -> lo <= 15 - db -> 0 <= v -> v + 2 ^ lo <= nd -> nd <= 65536 ->
  (forall j, 0 <= j < 2 ^ lo -> is_linkop (code_op (rdD (v + j))) = false /\ term_ok DISTS (15 - db) (rdD (v + j)) = true) ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 -> 0 <= da -> da + 4 * nd <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd rdD ->
  (forall R' (H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x [H'] ->
     0 <= H' -> H' < 2 ^ (b1 + 8 * (n - c1)) -> b1 + 8 * (n - c1) <= 29 -> b1 + 8 * (n - c1) <= 8 * n ->
     keptc Rb l R' KS_D2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
       [q + ci'; n - ci'; B'; B'; H'; da + 4 * (v + Z.land H' m2 / 2 ^ db); code_bits (rdD (v + Z.land H' m2 / 2 ^ db))] ->
     ci < ci' -> ci' <= n -> B' = b1 + 8 * (ci' - c1) -> B' <= 37 -> db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)) <= B' ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_D2 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D8BC (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DLOOP2 (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros Rb l M MD T q n da nd db lo v m2 c1 b1 ci B H fin rdD Hh RH
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt HH1 HH2 HBc Hm2 Hdb1 Hdb2 Hlo1 Hlo2 Hv1 Hv2 Hnd SUB
    Hq1 Hn26 Hq2 Hda1 Hda2 Hin Rfin Htab KX KD; [lia|].
  open_lists3.
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
  { (* no input left: ONE RUN to the leave stub *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end);
      [ split_lists3 | .. ]; try zreg; try lia.
    - replace (b1 + 8 * (n - c1)) with B by lia. lia.
    - keptc_close. }
  pose proof (Rfin ci ltac:(lia)) as Rb1.
  (* THE PULLED BYTE's VALUE EQUATION is stated before the run (no hint for it); the model's facts of the new
     accumulator value are said before the run too, at the value as the run leaves it *)
  pose proof (shl_byte (fin ci) B ltac:(lia) ltac:(lia)) as E1.
  pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]. rewrite pow2_add8 in Hp1 by lia.
  pose proof (land_mask_r (Z.shiftl (fin ci) (B mod 64) + H) (db + lo) ltac:(lia)) as Rm. rewrite <- Hm2 in Rm.
  pose proof (JR (Z.shiftl (fin ci) (B mod 64) + H)) as Rj1.
  destruct (SUB _ Rj1) as [_ TM1]. apply term_ok_DISTS in TM1 as [Hbits1 _].
  (* ONE RUN through the loop's body to its exit test, with THREE VALUE HINTS (the second-level index: its
     shift, its sum's order, its scaling: the table load's address must be read and the loaded entry must
     stand at the model's index) *)
  zto_branch_hq Rfd (first [ zhint srlw_small | zhint div_add_comm | zhint zext32_shr30 ]).
  set (H' := Z.shiftl (fin ci) (B mod 64) + H) in *.
  assert (HH' : 0 <= H' < 2 ^ (B + 8)) by (subst H'; rewrite pow2_add8 by lia; lia). clearbody H'. clear Hp0 Hp1 E1.
  pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  destruct (Z_lt_dec (B + 8) (db + code_bits (rdD (v + Z.land H' m2 / 2 ^ db)))) as [Hmore | Hdone].
  - (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (IH Rx lx Mx MD T q n da nd db lo v m2 c1 b1 (ci + 1) (B + 8) H' fin rdD Hh) end);
      [ split_lists3 | .. ]; try zreg; try lia; try eassumption.
    + intros R' ci' B' H'' RH' X1 X2 X3 X4 X5 X6 X7 X8 HK.
      eapply (KD R' ci' B' H''); try assumption; try lia. all: keptc_chain HK.
  - (* enough bits: ONE RUN to the continuation *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) H') end);
      [ split_lists3 | .. ]; try zreg; try lia.
    all: keptc_close.
Qed.

Lemma x_loop {RCa1 : RunCtx}  : forall (N : nat) (pc pcx : Z) Rb l M MD T (q n ext c0 b0 ci B H : Z) (fin : Z -> Z),
  ((pc = L_LXLOOP /\ pcx = L_LX60) \/ (pc = L_DXLOOP /\ pcx = L_DX80)) ->
  m_halted MD = None ->
  rholdsv Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x [ext; n - ci; q + ci; B; H; n - c0; b0; q + c0] ->
  n - ci < Z.of_nat N -> 0 <= c0 -> c0 <= ci -> ci <= n -> 0 <= b0 -> B = b0 + 8 * (ci - c0) ->
  B < ext -> ext <= 15 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
  1 <= q -> n < 67108864 -> q + n <= 140737488355328 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin -> (forall i, 0 <= i < n -> 0 <= fin i < 256) ->
  (forall R' (H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx [H'] ->
     0 <= H' -> H' < 2 ^ (b0 + 8 * (n - c0)) -> b0 + 8 * (n - c0) <= 14 -> b0 + 8 * (n - c0) <= 8 * n ->
     keptc Rb l R' KS_X ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_EXT (zupd R' []) M MD) T) ->
  (forall R' (ci' B' H' : Z),
     rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd [q + ci'; n - ci'; B'; H'] ->
     ci < ci' -> ci' <= n -> B' = b0 + 8 * (ci' - c0) -> ext <= B' -> B' <= 22 ->
     0 <= H' -> H' < 2 ^ B' -> B' <= 8 * ci' ->
     keptc Rb l R' KS_X ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pcx (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  induction N as [|N IH]; intros pc pcx Rb l M MD T q n ext c0 b0 ci B H fin Hpc Hh RH
    HN Hc0 Hc1 Hc2 Hb0 HB Hlt Hext HH1 HH2 HBc Hq1 Hn26 Hq2 Hin Rfin KX KD; [lia|].
  open_lists3.
  zkeys. unfold L_LXLOOP, L_LX60, L_DXLOOP, L_DX80, L_LVX_EXT in *. pose proof two64_eq as TW64.
  pose proof (pow2_48 B ltac:(lia)) as HPB. pose proof (pow2_48 (B + 8) ltac:(lia)) as HPB8.
  (* the loop's head is bound from the goal (the induction hypothesis is said for that head), so that the back
     edge's run stops there and nowhere else *)
  destruct Hpc as [[-> ->] | [-> ->]]; (
    lazymatch goal with |- realizes _ (zcfg _ ?PH _ _ _) _ =>
    destruct (Z.eq_dec (n - ci) 0) as [Hz | Hnz];
    [ (* no input left: ONE RUN to the leave stub *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KX Rx H) end);
      try (split_lists3; zreg); try zreg; try lia;
      [ replace (b0 + 8 * (n - c0)) with B by lia; lia | keptc_close ]
    | pose proof (Rfin ci ltac:(lia)) as Rb1;
      (* THE PULLED BYTE's VALUE EQUATION is stated before the run (no hint) *)
      pose proof (shl_byte (fin ci) B ltac:(lia) ltac:(lia)) as E1;
      pose proof (hold_pull1 H B (fin ci) ltac:(lia) ltac:(lia) Rb1) as [Hp0 Hp1]; rewrite pow2_add8 in Hp1 by lia;
      assert (HH' : 0 <= H + fin ci * 2 ^ B < 2 ^ (B + 8)) by (rewrite pow2_add8 by lia; lia);
      (* ONE RUN through the loop's body to its exit test *)
      zto_branch_q Rfd;
      destruct (Z_lt_dec (B + 8) ext) as [Hmore | Hdone];
      [ (* THE BACK EDGE: ONE RUN back to the loop's head, where the induction hypothesis applies *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx ?MDx) ?Tx =>
          eapply (IH PH _ Rx lx Mx MDx Tx q n ext c0 b0 (ci + 1) (B + 8) (H + fin ci * 2 ^ B) fin) end);
        [ first [left; split; reflexivity | right; split; reflexivity] | ..];
        try (split_lists3; zreg); try zreg; try lia; try eassumption;
        intros ? ? ? ? ? ? ? ? ? ? ? ? ? HK; eapply KD; try eassumption; try lia; keptc_chain HK
      | (* enough bits: ONE RUN to the continuation *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (KD Rx (ci + 1) (B + 8) (H + fin ci * 2 ^ B)) end);
        try (split_lists3; zreg); try zreg; try lia; keptc_close ] ] end).
Qed.



Definition tabsP {RCa1 : RunCtx}  (cx : ictx) (st : ist) (cf : Z -> Z) (M : mem) (na nd : Z) : Prop :=
  let la := cp_addr cx (t_lc st) in let da := cp_addr cx (t_dc st) in
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M la na (rdc cf (t_lc st)) /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M da nd (rdc cf (t_dc st)) /\
  tab_ok LENS (rdc cf (t_lc st)) (t_lb st) na = true /\ tab_ok DISTS (rdc cf (t_dc st)) (t_db st) nd = true /\
  0 < la /\ la + 4 * na <= c_zc cx /\ 0 < da /\ da + 4 * nd <= c_zc cx /\ na <= 2048 /\ nd <= 2048 /\
  la mod 2 = 0 /\ da mod 2 = 0 /\
  ZSEP (la + 4 * na <= c_ob cx \/ c_ob cx + c_osz cx <= la) /\ ZSEP (la + 4 * na <= c_p cx \/ c_p cx + 1384 <= la) /\
  ZSEP (da + 4 * nd <= c_ob cx \/ c_ob cx + c_osz cx <= da) /\ ZSEP (da + 4 * nd <= c_p cx \/ c_p cx + 1384 <= da) /\
  ZSEP (la + 4 * na <= c_p cx + 7160 \/ c_p cx + 7176 <= la) /\ ZSEP (da + 4 * nd <= c_p cx + 7160 \/ c_p cx + 7176 <= da) /\
  (65536 <= c_p cx -> 65536 <= la /\ 65536 <= da).

Lemma live_tabs {RCa1 : RunCtx}  : forall cx st lf cf M,
  ctx_ok ROMHI_S cx -> RNG cx st lf cf -> tables_live cx st cf -> rom_ok M ->
  mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
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
      exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf 0 o2 Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 4 M (p + 1384) 1444 cf o2 (nx - o2) Hcodes ltac:(lia) ltac:(lia) ltac:(lia)).
    + clear - ALp. Z.to_euclidean_division_equations; lia.
    + clear - ALp Ho2. Z.to_euclidean_division_equations; lia.
  -
    destruct TL as [Hlb Hdb]. subst lb db.
    exists 512, 32. unfold cp_addr, rdc. cbv [LENFIX_ADDR DISTFIX_ADDR].
    split_conj; try exact lenfix_ok; try exact distfix_ok; try (unfold ZSEP; lia).
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 67422 512 lenfix_f). { exact (rom_lenfix_arr M ROM). } exact lenfix_f_model.
    + apply (mem_arr_ext (run_segments R_segs rc_inp rc_sp rc_mb) 4 M 69470 32 distfix_f). { exact (rom_distfix_arr M ROM). } exact distfix_f_model.
    + reflexivity.
    + reflexivity.
Qed.

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

Ltac keptc_closeL := keptc_close.


Lemma stub_L1 {RCa1 : RunCtx}  : forall (pc : Z) Rb l M MD T (q n c0 b0 u rv : Z),
  (pc = L_LVX_L1 \/ pc = L_LVX_EXT) -> m_halted MD = None ->
  rholds (qargs [n - c0; b0; q + c0; u]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_l1 ->
  0 <= n - c0 -> n - c0 < 4294967296 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -160) rv ->
  (forall R', rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k [b0 + 8 * (n - c0); q + n; 0; rv] ->
     keptc Rb l R' KS_L1 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) pc (zupd Rb l) M MD) T.
Proof.
  intros pc Rb l M MD T q n c0 b0 u rv Hpc Hh RH H1 H2 Hrv K.
  open_lists3.
  zkeys. unfold L_LVX_L1, L_LVX_EXT, L_LEAVE in *.
  (* THE TWO VALUE EQUATIONS (the count times eight; the count's zero-extension) are stated before the runs *)
  assert (Ea : Z.shiftl (n - c0) 3 = 8 * (n - c0)) by (apply shiftl_3).
  pose proof (zext32_shift (n - c0) ltac:(lia)) as Eb.
  destruct Hpc as [-> | ->].
  - (* ONE RUN to the leave place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end);
      [ split_lists3 | ]; try zreg. keptc_closeL.
  - (* ONE RUN to the leave place *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end);
      [ split_lists3 | ]; try zreg. keptc_closeL.
Qed.

Lemma stub_L2 {RCa1 : RunCtx}  : forall Rb l M MD T (q n c1 b1 : Z),
  m_halted MD = None ->
  zget_l Rb l kA2 = n - c1 -> zget_l Rb l kA3 = b1 -> zget_l Rb l kS10 = q + c1 ->
  0 <= n - c1 -> n - c1 < 4294967296 ->
  (forall R', rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k [b1 + 8 * (n - c1); q + n; 0] ->
     keptc Rb l R' KS_L2 -> realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVE_LD (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L2 (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T q n c1 b1 Hh La2 La3 Ls11 H1 H2 K.
  zkeys. unfold L_LVX_L2, L_LEAVE_LD in *.
  (* THE TWO VALUE EQUATIONS are stated before the run *)
  assert (Ea : Z.shiftl (n - c1) 3 = 8 * (n - c1)) by (apply shiftl_3).
  pose proof (zext32_shift (n - c1) ltac:(lia)) as Eb.
  (* ONE RUN to the leave place *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (K Rx) end);
    [ split_lists3 | ]; try zreg.
  keptc_close.
Qed.

Definition st_w3 (st : ist) (len off ex : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      len off ex (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Local Ltac st_rest_set_tac :=
  intros cx st M v H Hp1 Hp2; destruct cx, st; unfold st_rest, st_w3 in *; icx_cbn;
  pose proof two64_eq as TW64;
  dand H as (A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17);
  repeat split;
  first [ apply mem_u32_stored; clear - Hp1 Hp2; lia_std
        | (apply mem_u64_frame || apply mem_u32_frame); [assumption | clear - Hp1 Hp2; unfold zdisj; rewrite length_Z_to_le_bytes'; cbn; lia_std] ].
Lemma st_rest_set92 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st v (t_offset st) (t_extra st)) (wbytes M (w64 (c_p cx + 108)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set96 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) v (t_extra st)) (wbytes M (w64 (c_p cx + 112)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
Lemma st_rest_set100 {RCa1 : RunCtx}  : forall cx st M v,
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> 0 <= c_p cx -> c_p cx + 7176 <= two64 ->
  st_rest (run_segments R_segs rc_inp rc_sp rc_mb) cx (st_w3 st (t_length st) (t_offset st) v) (wbytes M (w64 (c_p cx + 116)) (Z_to_le_bytes 4 v)).
Proof. st_rest_set_tac. Qed.
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

Ltac prune_rng :=
  repeat match goal with
  | H : _ < 4294967296 |- _ => clear H | H : 0 <= _ < 18446744073709551616 |- _ => clear H | H : _ < 18446744073709551616 |- _ => clear H
  | H : - 2147483648 <= _ |- _ => clear H | H : _ < 2147483648 |- _ => clear H | H : - 2147483648 <= _ < 2147483648 |- _ => clear H
  end.
End S_DistL.

Module S_DistX.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL S_Match S_DistL.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's TWO OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Notation L_DX20 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DX20 (only parsing).
Notation L_DXBC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DXBC (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholdsv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv (only parsing).

(* THE MODULE's REGISTER MAP: which register holds which of the values that the definition binds is the layout's
   list; the values, in the list's order of numbering: the stream's address, the two entry values, the state's
   address, the next output address, the output room left, the input left, the bit count, the next input address,
   the output count at the pass's entry *)
Definition x_regs (u p q n ob osz : Z) (K0 : positive -> Z) (cin cout bits out : Z) (R : tree Z) : Prop :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [u; K0 kGP; K0 kTP; p; ob + cout; osz - cout; n - cin; bits; q + cin; out])
    R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_xr.
Ltac open_xregs H :=
  unfold x_regs in H;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_xr JTAB_ADDR] in H;
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in H;
  destr_conj H; zgetl_nil.
Ltac close_xregs :=
  unfold x_regs;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_xr JTAB_ADDR];
  split_conj; zreg.

(* OPENERS OF THE LIST FORM for this module (they only unfold, split and name): the lists of module 3 and this
   module's two *)
Ltac open_lists4 :=
  repeat match goal with
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xh OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j80] in HL;
             destr_conj HL
         end.
Ltac split_lists4 :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_l1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xh OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j80];
  split_conj.

Theorem distext_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DISTEXT -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> zget_l Rb l kA3 = t_extra st -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DX20 (zupd Rb l) M MD) T.
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
    x_regs u p q n ob osz K0 ci cout B out R' -> rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xh [H] ->
    cin <= ci -> ci <= n -> 0 <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits -> 0 <= off -> off < 98304 ->
    s_std (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M' ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 8) DISTEXT ->
    st_rest (run_segments R_segs rc_inp rc_sp rc_mb) (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_ret (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    s_out (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
      (IST DISTEXT last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext) M' ->
    mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 168) 320 lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 1384) 1444 cf ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X [(u - 1024, 1024); (u, 112); (p, 7176); (ob, osz)]) M' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DXBC (zupd R' []) M' MD) T).
  { intros R' M' ci H B off XR G24 Hc1 Hc2 HB1 HB2 HH1 HH2 HBc HWm Ho1 Ho2 STD' Hm' SR' RET' OUT' HL' HC' HAG'.
    open_xregs XR. open_lists4. zgetl_nil. unfold L_DXBC.
    clear S72 Hback ROM Wstk Wp Wob Ww FRM CST HK Hin Hmode SREST SRET SOUT Hlens Hcodes HAG.
    pose proof STD' as STD2. open_std STD2. icx_cbn. zkeys.
    clear Hm'.
    pose proof (sinv_pull _ _ lf cf ci H B SI0 ltac:(cbn; lia) ltac:(cbn; lia) HB1 HB2 HH1 HH2 HBc ltac:(cbn; lia)) as [SI1 ME1].
    pose proof (sinv_to_match _ _ lf cf off SI1 eq_refl Ho1 Ho2) as [SI2 ME2].
    unfold st_pull, st_dx in SI2, ME2, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2, ME1.
    (* ONE RUN to the copy arm's entry *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (match_s _ fin MD T M0 Rx lx Mx
                (IST MATCH last flags ci cout H B out ret length off extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end).
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: cbv [MATCH]; first [assumption | exact I].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (J80 : forall R' (ci H B : Z),
    x_regs u p q n ob osz K0 cin cout bits out R' ->
    rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j80 [q + ci; n - ci; B; H; extra] ->
    cin <= ci -> ci <= n -> extra <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci -> B = bits + 8 * (ci - cin) ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DX80 (zupd R' []) M MD) T).
  { intros R' ci H B XR RH Hc1 Hc2 HxB HB40 HH1 HH2 HBc HB.
    open_xregs XR. open_lists4. zgetl_nil. zkeys. clear KL. unfold L_DX80.
    repeat match goal with H : forall i : Z, _ |- _ => clear H end.
    pose proof SREST as C96. unfold st_rest in C96. icx_cbn. dand C96 as (_ & _ & _ & _ & _ & C96 & _).
    pose proof (pow2_15 extra ltac:(lia)) as HPx.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    (* the model's facts and the shifted accumulator's VALUE EQUATION are stated before the run *)
    pose proof (land_mask_r H extra ltac:(lia)) as Rbx.
    pose proof (srl_hold H B extra ltac:(lia) ltac:(lia) ltac:(lia)) as Es.
    pose proof (hold_shr_bound H B extra ltac:(lia) ltac:(lia)) as HH'.
    (* the state's relation is carried over the run's first store before the run, at the value the store writes *)
    st_prestore st_rest_set96 (offset + Z.land H (2 ^ extra + -1)) SREST.
    (* ONE RUN to the join point, with ONE VALUE HINT (the mask of the extra bits: the masked value is added,
       made small and stored) *)
    zuntil_h Rfd (first [ zhint mask_not_sllw ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
         eapply (JBC Rx Mx ci (H / 2 ^ extra) (B - extra) (offset + Z.land H (2 ^ extra - 1))) end);
      try (split_lists4; zreg); try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  destruct (Z.eq_dec extra 0) as [Hx0 | Hx1].
  { (* no extra bits: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ => eapply (JBC Rx Mx cin hold bits offset) end);
      try (split_lists4; zreg); try zreg; try lia; try assumption.
    - close_xregs.
    - close_std. }
  (* ONE RUN to the test of the bits in hand *)
  zto_branch_q Rfd.
  destruct (Z_lt_dec bits extra) as [Hneed | Hhave].
  - (* more bits wanted: ONE RUN to the extra-bits loop's head *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (x_loop (S (Z.to_nat (n - cin))) L_DXLOOP L_DX80 Rx lx Mx MD T q n extra cin bits cin bits hold fin) end);
      try (split_lists4; zreg); try zreg; try lia; try eassumption.
    +
      intros R' H' G24 HH1 HH2 HB14 HBn KP. keptc_open KP. open_lists4. zgetl_nil. zimps.
      eapply (stub_L1 L_LVX_EXT R' [] M MD T q n cin bits u ret); [right; reflexivity | exact Hh | split_lists4; zreg | lia | lia | exact SRET |].
      intros R9 RH9 HK9. keptc_open HK9. open_lists4. zgetl_nil. zimps.
      pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
      unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
        t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
      unfold KLEAVE, L_LEAVE in KL.
      eapply (KL R9 M _ ret lf cf SI1).
      * unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
      * close_std.
      * split; [exact Hmode | exact SREST].
      * first [ exact SOUT | exact I ].
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' ci' B' H' RH' X1 X2 X3 X4 X5 X6 X7 X8 KP. keptc_open KP. open_lists4. zgetl_nil.
      zimps.
      eapply (J80 R' ci' H' B'); try (split_lists4; zreg); try assumption; try lia. close_xregs.
  - (* enough bits: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J80 Rx cin hold bits) end);
      try (split_lists4; zreg); try zreg; try lia.
    close_xregs.
Qed.

Theorem arm_DISTEXT {RCa1 : RunCtx}  : arm_stmt L_DISTEXT DISTEXT.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  pose proof KM as KM0. open_kmem KM. destruct SAT as [Hmode SREST].
  pose proof SREST as SR0. unfold st_rest in SR0. dand SR0 as (_ & _ & _ & _ & _ & _ & C100 & _).
  dand RG as (FIX & VARS & G27). pose proof FIX as FIX0. unfold s_fix in FIX. destr_conj FIX.
  zkeysb. unfold L_DISTEXT in *.
  pose proof SI as SI'. dand SI' as (R & _ & _ & Mo).
  assert (HX : 0 <= t_extra st <= 15).
  { dand Mo as (_ & _ & _ & _ & _ & _ & _ & Mde & _). destruct (Mde Hmd) as [A _].
    unfold RNG in R. destr_conj R. split; [assumption | exact A]. }
  (* ONE RUN to the arm's inner entry *)
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) _ _) _ =>
    eapply (distext_s cx fin MD T M0 Rx lx M st lf cf CX Hh Hfin Hmd SI) end).
  - split; [exact FIX0 | split; [exact VARS | zreg]].
  - cbv [zget_l alookup Pos.eqb]. rewrite ?swrap32_small by lia. reflexivity.
  - exact KM0.
  - exact K.
Qed.
End S_DistX.

Module S_Dist.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInvTab.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import S_MatchL S_Match S_DistL S_DistX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* THE MODULE's TWO OWN LABELS ARE FIELDS OF THE IMAGE's LAYOUT TEXT; here they have their short names only *)
Notation L_D8EC := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_D8EC (only parsing).
Notation L_DBAD := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_DBAD (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholdsv := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv (only parsing).

(* THE MODULE's REGISTER MAP: which register holds which of the values that the definition binds is the layout's
   list; the values, in the list's order of numbering: the stream's address, the two entry values, the state's
   address, the next output address, the output room left, the output count at the pass's entry *)
Definition d_regs (u p ob osz : Z) (K0 : positive -> Z) (cout out : Z) (R : tree Z) : Prop :=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
    (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs [u; K0 kGP; K0 kTP; p; ob + cout; osz - cout; out])
    R [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_dr.
Ltac open_dregs H :=
  unfold d_regs in H;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_dr JTAB_ADDR] in H;
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in H;
  destr_conj H; zgetl_nil.
Ltac close_dregs :=
  unfold d_regs;
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_dr JTAB_ADDR];
  split_conj; zreg.
Ltac mode_getr Mo := clear - Mo; unfold MODE in Mo; icx_cbn; repeat match goal with H : _ /\ _ |- _ => destruct H end;
  first [ assumption | match goal with H : ?x = ?x -> _ |- _ => exact (H eq_refl) end ].
(* OPENERS OF THE LIST FORM for this module (they only unfold, split and name): the lists of modules 3 and 4 and this
   module's four; an opened fact stands with its register's key number *)
Ltac open_lists5 :=
  repeat match goal with
         | HL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ |- _ =>
             cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xh OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j80
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8ec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_kx1
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j04 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8bc
                  kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in HL;
             destr_conj HL
         end.
Ltac split_lists5 :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d1d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_d2d
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_x OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xx OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l1k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_l2k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_lenf_l1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_xh OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j80
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8ec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_kx1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j04 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8bc];
  split_conj.
(* the closing word of an application's premises: each premise by the closer that fits its form *)
Ltac jfin :=
  lazymatch goal with
  | |- OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholdsv _ _ _ _ => split_lists5; zreg
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
Ltac kcbv_in H := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in H.

Lemma land_mask_l' : forall x k, 0 <= k -> 0 <= Z.land (2 ^ k + -1) x < 2 ^ k.
Proof. intros x k Hk. replace (2 ^ k + -1) with (2 ^ k - 1) by lia. apply land_mask_l. exact Hk. Qed.
(* A SMALL HINT LEMMA (new in the run form): the mask of k low bits, with its right side in the form the model's
   facts of this module are said in. A run's hint names it. *)
Lemma mask_not_sllw_m1 : forall k, 0 <= k <= 30 ->
  Z.lxor (bv_swrap 32 (Z.shiftl (-1) (k mod 32))) (-1) = 2 ^ k + -1.
Proof. intros k Hk. rewrite mask_not_sllw by lia. lia. Qed.

Theorem dist_s {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_S cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = DIST -> sinv cx st lf cf ->
  s_regs_d10 cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_DIST (zupd Rb l) M MD) T.
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
    d_regs u p ob osz K0 cout out R' ->
    rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8ec
      [-16180; 30; 67008; p + 7160; code_op e; code_val e; code_bits e; B; H; ab; q + ci; n - ci] ->
    1 <= code_bits e ->
    ((16 <= code_op e < 32 /\ 1 <= code_val e /\ code_val e + Z.shiftl 1 (code_op e - 16) - 1 <= 32768 /\ code_op e <= 29)
     \/ (Z.land (code_op e) 64 <> 0 /\ Z.land (code_op e) 16 = 0 /\ Z.land (code_op e) 32 = 0)) ->
    cin <= ci -> ci <= n -> code_bits e <= B -> B <= 40 -> 0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    8 * (n - ci) + B <= 8 * (n - cin) + bits ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D8EC (zupd R' []) M MD) T).
  { intros R' ci B H e ab DR RH Hbe CLS Hc1 Hc2 HbB HB40 HH1 HH2 HBc HWm.
    open_dregs DR. open_lists5. zgetl_nil. unfold L_D8EC.
    clear S104 S96 S72 HtD KL KLL.
    pose proof (code_op_range e) as Rop. pose proof (code_val_range e) as Rval. pose proof (code_bits_range e) as Rbi.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    (* THE SHIFTED ACCUMULATOR's VALUE EQUATION is stated before the run (no hint) *)
    pose proof (srl_hold H B (code_bits e) ltac:(lia) ltac:(lia) ltac:(lia)) as Es.
    pose proof (hold_shr_bound H B (code_bits e) ltac:(lia) ltac:(lia)) as HH'.
    (* ONE RUN to the test of the entry's kind *)
    zto_branch_q Rfd.
    pose proof (sinv_pull _ _ lf cf ci (H / 2 ^ code_bits e) (B - code_bits e) SI0 ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as [SI1 ME1].
    unfold st_pull in SI1, ME1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1, ME1.
    destruct CLS as [(Hop16 & Hv1 & Hv32k & Hop29) | (H64 & H16 & H32)].
    2: {
      pose proof (land_range_r (code_op e) 64 ltac:(lia)) as R64.
      unfold KBADMSG_A3, L_BADMSG_A3 in KBA3.
      (* a bad entry: ONE RUN to the error place *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KBA3 Rx Mx (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                              lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf) end).
      (* the continuation's premises are closed each by the closer that fits it *)
      all: first
        [ (apply sinv_bad_of; exact SI1)
        | (pose proof (meas_bad_of (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                         (IST DIST last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length offset extra
                              lc dc lb db ncode nlen ndist shave nx whave wnext)) as MB;
           cbn [t_mode] in MB; change (rank DIST) with 16 in MB; clear - MB ME1; lia)
        | (unfold s_fix; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg)
        | zreg
        | (cbv [kA3]; rewrite TW64; zreg)
        | (unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]; split_conj; try assumption; try close_std;
           first [exact SREST | exact SRET | exact SOUT | exact I | exact HAG]) ]. }
    pose proof (op_base_tests (code_op e) ltac:(lia)) as (T16 & T64 & T32 & T240 & T15 & Tnz).
    (* THE EXTRA COUNT's VALUE EQUATION is stated before the run (no hint) *)
    assert (T15' : Z.land (code_op e) 15 = code_op e - 16) by lia.
    pose proof (sinv_to_distext _ _ lf cf (code_val e) (code_op e - 16) SI1 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [SI2 ME2].
    unfold st_dx in SI2, ME2. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI2, ME2.
    unfold L_DX20 in *.
    (* the state's relation is carried over the run's two field stores before the run, at the values the stores write *)
    st_prestore st_rest_set96 (code_val e) SREST.
    st_prestore st_rest_set100 (Z.land (code_op e) 15) SREST.
    (* ONE RUN to the next arm's inner entry *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (distext_s _ fin MD T M0 Rx lx Mx
                (IST DISTEXT last flags ci cout (H / 2 ^ code_bits e) (B - code_bits e) out ret length (code_val e) (code_op e - 16)
                     lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf CX0 Hh Hfin eq_refl SI2) end).
    all: try rewrite T15' in SREST.
    - unfold s_regs_d10, s_fix, s_vars; icx_cbn; zkeys; cbv [JTAB_ADDR]; split_conj; zreg.
    - zreg.
    - unfold k_mem, st_at; icx_cbn; cbv [N_LENS N_CODES]. split_conj; try assumption; try close_std.
      all: first [cbv [DISTEXT]; assumption | exact SREST | exact SRET | exact SOUT | exact I | exact HAG].
    - eapply KALL_mono; [| exact K]. clear - ME1 ME2. cbn [t_mode] in *. lia. }
  assert (KX1 : forall R' (H' : Z),
    rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_kx1 [H'; n - cin; bits; q + cin] ->
    0 <= H' -> H' < 2 ^ (bits + 8 * (n - cin)) -> bits + 8 * (n - cin) <= 14 -> bits + 8 * (n - cin) <= 8 * n ->
    d_regs u p ob osz K0 cout out R' ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LVX_L1 (zupd R' []) M MD) T).
  { intros R' H' RH HH1 HH2 HB14 HBn DR. open_dregs DR. open_lists5. zgetl_nil. unfold L_LVX_L1.
    clear J8EC KBA3 KLL.
    eapply (stub_L1 L_LVX_L1 R' [] M MD T q n cin bits u ret); [left; reflexivity | exact Hh | split_lists5; zreg | lia | lia | exact SRET |].
    intros R9 RH9 KP. keptc_open KP. open_lists5. zgetl_nil. zimps.
    pose proof (sinv_pull _ _ lf cf n H' (bits + 8 * (n - cin)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1 HH2 HBn ltac:(cbn; lia)) as [SI1 _].
    unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
      t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
    unfold KLEAVE, L_LEAVE in KL.
    eapply (KL R9 M _ ret lf cf SI1).
    - unfold s_regs_leave; icx_cbn; zkeys; split_conj; zreg.
    - close_std.
    - split; [exact Hmode | exact SREST].
    - first [ exact SOUT | exact I ].
    - exact Hlens.
    - exact Hcodes.
    - exact HAG. }
  assert (J04 : forall R' (ci B H : Z),
    d_regs u p ob osz K0 cout out R' ->
    rholdsv R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j04
      [-16180; 30; 67008; n - cin; bits; q + cin; da; 2 ^ db + -1; q + ci; n - ci; B; H;
       da + 4 * Z.land (2 ^ db + -1) H; code_bits (rdD (Z.land (2 ^ db + -1) H))] ->
    cin <= ci -> ci <= n -> B = bits + 8 * (ci - cin) -> code_bits (rdD (Z.land (2 ^ db + -1) H)) <= B -> B <= 40 ->
    0 <= H -> H < 2 ^ B -> B <= 8 * ci ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D04 (zupd R' []) M MD) T).
  { intros R' ci B H DR RH Hc1 Hc2 HB HbB HB40 HH1 HH2 HBc.
    open_dregs DR. open_lists5. zgetl_nil. unfold L_D04.
    clear KX1 KL.
    set (i := Z.land (2 ^ db + -1) H) in *.
    pose proof (land_mask_l' H db ltac:(lia)) as Ri. fold i in Ri.
    pose proof (tab_root_entry DISTS rdD db nd i TOKD Ri) as (Hbits & _ & _ & CASES).
    pose proof (code_op_range (rdD i)) as Rop. pose proof (code_val_range (rdD i)) as Rval.
    assert (HPB : 1 <= 2 ^ B <= 2 ^ 40) by (split; [pose proof (pow2_pos B ltac:(lia)); lia | apply pow2_le; lia]).
    (* ONE RUN (the entry's two table loads) to the test of the entry's kind *)
    zto_branch_q Rfd.
    destruct CASES as [[NL TM] | (L1 & L2 & L3 & L4 & SUB)].
    -
      apply term_ok_DISTS in TM as [Hb1 CLS].
      assert (Hop16 : 16 <= code_op (rdD i)).
      { destruct CLS as [(A & _) | (A64 & _ & _)]; [lia|].
        apply is_linkop_false in NL. pose proof (land_range_r (code_op (rdD i)) 64 ltac:(lia)).
        destruct (Z_lt_dec (code_op (rdD i)) 16); [|lia]. exfalso.
        assert (E : code_op (rdD i) = 0) by lia. rewrite E in A64. apply A64. reflexivity. }
      (* a final entry: ONE RUN to the join point *)
      zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8EC Rx ci B H (rdD i)) end).
      all: jfin.
    -
      match goal with HG : zget R' _ = code_bits (rdD i) |- _ => rewrite L2 in HG end.
      pose proof (op_link_tests (code_op (rdD i)) ltac:(lia)) as (T16 & T64 & T240 & Tnz).
      assert (HPm : 1 <= 2 ^ (db + code_op (rdD i)) <= 32768) by (apply pow2_15; lia).
      pose proof (pow2_15 (code_op (rdD i)) ltac:(lia)) as HPlo.
      (* the model's facts of the second-level index are said before the run, with the mask written out *)
      assert (JR : forall Hx, 0 <= Z.land Hx (2 ^ (db + code_op (rdD i)) + -1) / 2 ^ db < 2 ^ code_op (rdD i)).
      { intros Hx. pose proof (land_mask_r Hx (db + code_op (rdD i)) ltac:(lia)) as A.
        change (2 ^ (db + code_op (rdD i)) - 1) with (2 ^ (db + code_op (rdD i)) + -1) in A.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. exact (proj2 A). }
      pose proof (land_mask_r H (db + code_op (rdD i)) ltac:(lia)) as Rm.
      change (2 ^ (db + code_op (rdD i)) - 1) with (2 ^ (db + code_op (rdD i)) + -1) in Rm.
      pose proof (JR H) as Rj.
      destruct (SUB _ Rj) as [NL2 TM2]. pose proof TM2 as TM2'. apply term_ok_DISTS in TM2 as [Hbits2 CLS2].
      (* ONE RUN to the test of the bits in hand, with FOUR VALUE HINTS (the mask; the second-level index: its
         shift, its sum's order, its scaling: the table load's address must be read and the loaded entry must stand
         at the model's index) *)
      zto_branch_hq Rfd (first [ zhint mask_not_sllw_m1 | zhint srlw_small | zhint div_add_comm | zhint zext32_shr30 ]).
      set (m2 := 2 ^ (db + code_op (rdD i)) + -1) in *.
      set (v := code_val (rdD i)) in *. set (lo := code_op (rdD i)) in *.
      assert (J8BC : forall R2 (ci2 B2 H2 : Z),
        d_regs u p ob osz K0 cout out R2 ->
        rholdsv R2 [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.rl_lenf_j8bc
          [q + cin; da; db; v; p + 7160; n - ci; B; q + ci; q + ci2; n - ci2; B2; H2;
           da + 4 * (v + Z.land H2 m2 / 2 ^ db); code_bits (rdD (v + Z.land H2 m2 / 2 ^ db))] ->
        ci <= ci2 -> ci2 <= n -> B2 = bits + 8 * (ci2 - cin) -> db + code_bits (rdD (v + Z.land H2 m2 / 2 ^ db)) <= B2 -> B2 <= 40 ->
        0 <= H2 -> H2 < 2 ^ B2 -> B2 <= 8 * ci2 ->
        realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_D8BC (zupd R2 []) M MD) T).
      { intros R2 ci2 B2 H2 DR2 RH2 Hd1 Hd2 HB2 HbB2 HB2' HH21 HH22 HBc2.
        open_dregs DR2. open_lists5. zgetl_nil. unfold L_D8BC.
        clear KLL.
        pose proof (JR H2) as Rj2.
        set (j2 := Z.land H2 m2 / 2 ^ db) in *.
        assert (HPB2 : 1 <= 2 ^ B2 <= 2 ^ 40) by (split; [pose proof (pow2_pos B2 ltac:(lia)); lia | apply pow2_le; lia]).
        pose proof (code_bits_range (rdD (v + j2))) as Rb2.
        (* THE SHIFTED ACCUMULATOR's VALUE EQUATION and the model's facts are stated before the run (no hint) *)
        pose proof (srl_hold H2 B2 db ltac:(lia) ltac:(lia) ltac:(lia)) as Es2.
        pose proof (hold_shr_bound H2 B2 db ltac:(lia) ltac:(lia)) as HH2'.
        destruct (SUB _ Rj2) as [NL3 TM3]. apply term_ok_DISTS in TM3 as [Hbits3 CLS3].
        (* ONE RUN (the entry's two table loads) to the join point *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ =>
          eapply (J8EC Rx ci2 (B2 - db) (H2 / 2 ^ db) (rdD (v + j2))) end).
        all: jfin. }
      destruct (Z_lt_dec B (db + code_bits (rdD (v + Z.land H m2 / 2 ^ db)))) as [Hneed | Hok].
      + (* more bits wanted: ONE RUN to the second table loop's head *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
          eapply (d_loop2 (S (Z.to_nat (n - ci))) Rx lx Mx MD T q n da nd db lo v m2 ci B ci B H fin rdD Hh) end).
        all: jfin.
        *
          intros R5 H' Q24 HH1' HH2' HB29 HBn KP. keptc_open KP. open_lists5. zgetl_nil. zimps.
          clear J8BC J8EC SUB JR.
          eapply (stub_L2 R5 [] M MD T q n ci B Hh); [zreg | zreg | zreg | lia | lia |].
          intros R9 RH9 KP9. keptc_open KP9. open_lists5. zgetl_nil. zimps.
          pose proof (sinv_pull _ _ lf cf n H' (B + 8 * (n - ci)) SI0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) HH1' HH2' HBn ltac:(cbn; lia)) as [SI1 _].
          unfold st_pull in SI1. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
            t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI1.
          unfold KLEAVE_LD, L_LEAVE_LD in KLL. zkeys.
          eapply (KLL R9 M _ lf cf SI1).
          -- unfold s_regs_leave_ld; icx_cbn; zkeys; split_conj; zreg.
          -- close_std.
          -- split; [exact Hmode | exact SREST].
          -- exact SRET.
          -- first [ exact SOUT | exact I ].
          -- exact Hlens.
          -- exact Hcodes.
          -- exact HAG.
        *
          intros R5 ci' B' H' RH5 X1 X2 X3 X4 X5 X6 X7 X8 KP. keptc_open KP. open_lists5. zgetl_nil.
          zimps.
          eapply (J8BC R5 ci' B' H'). all: jfin.
      + (* enough bits: ONE RUN to the join point *)
        zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J8BC Rx ci B H) end).
        all: jfin. }
  clear KBA3 KLL.
  pose proof SREST as SR0. unfold st_rest in SR0. icx_cbn. dand SR0 as (_ & _ & _ & _ & _ & _ & _ & _ & C112 & _ & C124 & _).
  rewrite <- Eda in C112. clear Eda.
  pose proof (land_mask_l' hold db ltac:(lia)) as Ri0.
  pose proof (tab_root_entry DISTS rdD db nd (Z.land (2 ^ db + -1) hold) TOKD Ri0) as (Hbits0 & _ & _ & _).
  (* ONE RUN to the test of the bits in hand, with TWO VALUE HINTS (the mask; the table index, scaled: the table
     load's address must be read) *)
  zto_branch_hq Rfd (first [ zhint mask_not_sllw_m1 | zhint shl2_mul4 ]).
  destruct (Z_lt_dec bits (code_bits (rdD (Z.land (2 ^ db + -1) hold)))) as [Hneed | Hok].
  - (* more bits wanted: ONE RUN to the first table loop's head *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?Rx ?lx) ?Mx _) _ =>
      eapply (d_loop1 (S (Z.to_nat (n - cin))) Rx lx Mx MD T q n da nd db (2 ^ db + -1) cin bits cin bits hold fin rdD Hh) end).
    all: jfin.
    + intros R' H' G24 HH1' HH2' HB14 HBn KP. keptc_open KP. open_lists5. zgetl_nil. zimps.
      eapply (KX1 R' H'). all: jfin.
    + intros R' ci' B' H' RH' X1 X2 X3 X4 X5 X6 X7 X8 KP. keptc_open KP. open_lists5. zgetl_nil.
      zimps.
      eapply (J04 R' ci' B' H'). all: jfin.
  - (* enough bits: ONE RUN to the join point *)
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?Rx _ _) _ => eapply (J04 Rx cin bits hold) end).
    all: jfin.
Qed.

Theorem arm_DIST {RCa1 : RunCtx}  : arm_stmt L_DIST DIST.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hmd SI RG KM K.
  eapply dist_s; try eassumption.
Qed.
End S_Dist.
