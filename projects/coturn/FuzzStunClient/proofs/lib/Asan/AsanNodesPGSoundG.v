(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesRP AsanNodesRPSoundG AsanNodesPG AsanWordLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan AsanNodesFX AsanNodesFSoundG AsanPGVal AsanPGValSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require RefEnframeArith.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition isrc_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (src s3v : Z) (regs : bvmap 5 word),
    0 <= src < 2 ^ 64 -> 1 <= s3v < 2 ^ 64 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall j, 0 <= j < 8 -> mem (Z_to_bv 64 ((RPN.SB + src / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
    (forall j, 0 <= j < 8 -> mem (Z_to_bv 64 ((RPN.SB + (s3v - 1) / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
    getr regs 11%bv = Z_to_bv 64 src -> getr regs 19%bv = Z_to_bv 64 s3v ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (PGN.ISRC_ENTRY T)) mem rom) (mkst regs' (Z_to_bv 64 (PGN.ISRC_EXIT T)) mem rom)
      /\ (forall r, r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 19%bv -> getr regs' r = getr regs r).

(* [comment removed for export] *)
Definition idst_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (p n : Z) (b1 : byte) (bs1 bs2 : list byte) (regs : bvmap 5 word),
    0 <= p -> p mod 8 = 0 -> 1 <= n <= 64 -> p + n < 2 ^ 47 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall i, 0 <= i < n / 8 -> mem (Z_to_bv 64 (RPN.SB + p / 8 + i)) = Some (Z_to_bv 8 0)) ->
    (n mod 8 <> 0 -> rdn SEGS mem (Z_to_bv 64 (RPN.SB + p / 8 + n / 8)) 1 = Some [b1] /\ n mod 8 <= bv_unsigned b1 <= 127) ->
    rdn SEGS mem (Z_to_bv 64 ((RPN.SB + p / 8) / 8 * 8)) 8 = Some bs1 ->
    rdn SEGS mem (Z_to_bv 64 ((RPN.SB + (p + n - 1) / 8) / 8 * 8)) 8 = Some bs2 ->
    getr regs 10%bv = Z_to_bv 64 p -> getr regs 20%bv = Z_to_bv 64 (p + n) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (PGN.IDST_ENTRY T)) mem rom) (mkst regs' (Z_to_bv 64 (PGN.IDST_EXIT T)) mem rom)
      /\ (forall x, x <> 13%bv -> x <> 14%bv -> x <> 15%bv -> x <> 16%bv -> x <> 17%bv -> x <> 20%bv -> getr regs' x = getr regs x).



(* [comment removed for export] *)
Definition pg_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (p n : Z) (regs : bvmap 5 word),
    0 <= p -> p mod 8 = 0 -> 1 <= n -> (p + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= p /\ p + n <= RPN.kHighEnd)) ->   (* [comment removed for export] *)
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    cell8 SEGS mem (RPN.rp_gfl T) (RPN.rp_cfl T) ->
    rdn SEGS mem (Z_to_bv 64 (RPN.rp_cfl T + 85)) 1 = Some [Z_to_bv 8 1] ->
    rdn SEGS mem (Z_to_bv 64 (RPN.rp_ccp T)) 1 = Some [Z_to_bv 8 1] ->
    store_ok SEGS mem (Z_to_bv 64 (RPN.SB + p / 8 + n / 8)) 1 = true ->
    getr regs 9%bv = Z_to_bv 64 n -> getr regs 22%bv = Z_to_bv 64 (8 * (n / 8)) -> getr regs 20%bv = Z_to_bv 64 p ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (PGN.PG_ENTRY T)) mem rom)
                  (mkst regs' (Z_to_bv 64 (PGN.PG_EXIT T))
                        (if (n mod 8 =? 0)%Z then mem
                         else wbytes mem (Z_to_bv 64 (RPN.SB + p / 8 + n / 8)) (word_to_le_bytes 1 (Z_to_bv 64 (n mod 8)))) rom)
      /\ (forall x, x <> 1%bv -> x <> 10%bv -> x <> 11%bv -> x <> 12%bv -> x <> 13%bv -> x <> 14%bv -> x <> 15%bv -> x <> 16%bv ->
                    x <> 17%bv -> x <> 22%bv -> getr regs' x = getr regs x).



(* [comment removed for export] *)
Definition rpp_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (beg n usp : Z) (regs : bvmap 5 word) (ra : word) (b1 : byte),
    16 <= n <= 2 ^ 40 -> 0 <= beg -> beg mod 8 = 0 ->
    (beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)) ->   (* [comment removed for export] *)
    80 <= usp < 2 ^ 64 ->
    RPN.SB + (beg + n - 1) / 8 < usp - 72 ->
    (forall i, 0 <= i < n / 8 -> mem (Z_to_bv 64 (RPN.SB + beg / 8 + i)) = Some (Z_to_bv 8 0)) ->
    (n mod 8 <> 0 -> rdn SEGS mem (Z_to_bv 64 (RPN.SB + beg / 8 + n / 8)) 1 = Some [b1] /\ bv_unsigned b1 = n mod 8) ->
    (forall a, usp - 72 <= a < usp -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = Z_to_bv 64 usp ->
    getr regs 10%bv = Z_to_bv 64 beg -> getr regs 11%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rp_entry T)) mem (seg_rom SEGS)) (mkst regs' ra mem' (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ (forall x : word, bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rpp_arith : forall beg n, 0 <= beg -> beg mod 8 = 0 -> 16 <= n ->
  (beg + n - 1) / 8 = beg / 8 + (n - 1) / 8
  /\ (n mod 8 = 0 -> (n - 1) / 8 = n / 8 - 1) /\ (n mod 8 <> 0 -> (n - 1) / 8 = n / 8)
  /\ (beg + n - 1) mod 8 = (if n mod 8 =? 0 then 7 else n mod 8 - 1) /\ 2 <= n / 8.
Proof. intros. destruct (Z.eqb_spec (n mod 8) 0); lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition rpin_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (beg n usp B N : Z) (regs : bvmap 5 word) (ra : word),
    16 <= n <= 2 ^ 40 -> 0 <= B -> B mod 8 = 0 -> N mod 8 = 0 -> B <= beg -> beg + n <= B + N ->
    (B + N <= RPN.kLowEnd \/ (RPN.kHighBeg <= B /\ B + N <= RPN.kHighEnd)) ->   (* [comment removed for export] *)
    80 <= usp < 2 ^ 64 ->
    RPN.SB + (B + N - 1) / 8 < usp - 72 ->
    (forall i, 0 <= i < N / 8 -> mem (Z_to_bv 64 (RPN.SB + B / 8 + i)) = Some (Z_to_bv 8 0)) ->
    (forall a, usp - 72 <= a < usp -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = Z_to_bv 64 usp ->
    getr regs 10%bv = Z_to_bv 64 beg -> getr regs 11%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rp_entry T)) mem (seg_rom SEGS)) (mkst regs' ra mem' (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ (forall x : word, bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rpin_arith : forall B N beg n, 0 <= B -> B mod 8 = 0 -> N mod 8 = 0 -> B <= beg -> beg + n <= B + N -> 1 <= n ->
  B / 8 <= beg / 8 /\ (beg + n - 1) / 8 <= B / 8 + N / 8 - 1 /\ beg / 8 <= (beg + n - 1) / 8.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).







(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable T : RPN.rptab.
Hypothesis IMG : rp_img SEGS T.
Hypothesis ISPEC : isrc_spec SEGS T.
Hypothesis DSPEC : idst_spec SEGS T.
Hypothesis PSPEC : pg_spec SEGS T.
Hypothesis RPPSPEC : rpp_spec SEGS T.
Hypothesis RPINSPEC : rpin_spec SEGS T.
Hypothesis SEGS_wr : segs_wr_ok SEGS.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma regs_ok_region : forall rs E sr R R' nx,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) rs -> getr R' r = getr R r) ->
  regs_ok (ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R'.
Proof.
  induction rs as [|r rest IH]; intros E sr R R' nx HR Hsr Hrs Hout; cbn [sr_fresh map ext_list].
  - apply regs_ok_pointwise. intros x Hx. rewrite (Hout x Hx ltac:(intros [])). pose proof (HR x) as Hx'.
    unfold sr_get in Hx'. destruct (bv_eqb x 0%bv) eqn:E0; [|exact Hx'].
    exfalso. apply Hx. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0.
  - apply Forall_cons_iff in Hrs as [Hr Hrest].
    set (rb := Z_to_bv 5 (Z.of_nat r)).
    assert (Hrb : ridx rb = r) by (unfold rb; apply ridx_lit; lia).
    assert (Hrb0 : rb <> 0%bv).
    { intros X. apply (f_equal ridx) in X. rewrite Hrb in X. cbv in X. lia. }
    apply (IH (ext1 E nx (getr R' rb)) (sr_upd sr r (EVar nx)) (regupd R rb (getr R' rb)) R' (N.succ nx)).
    + apply regs_ok_pointwise. intros x Hx.
      pose proof (regs_ok_agree' nx E (ext1 E nx (getr R' rb)) sr R (ext1_agree _ _ _) Hsr HR) as HR1.
      destruct (bv_eq_dec 5 x rb) as [->|NE].
      * rewrite getr_same by exact Hrb0. rewrite Hrb. rewrite nth_sr_upd, Nat.eqb_refl. cbn [edenot]. rewrite ext1_at. reflexivity.
      * rewrite getr_other by (exact NE). rewrite nth_sr_upd.
        assert (Hne : Nat.eqb (ridx x) r = false).
        { first [apply Nat.eqb_neq | apply N.eqb_neq]. intros X. apply NE. apply ridx_inj. rewrite Hrb. exact X. }
        rewrite Hne. pose proof (HR1 x) as Hx1. unfold sr_get in Hx1. destruct (bv_eqb x 0%bv) eqn:E0; [|exact Hx1].
        exfalso. apply Hx. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0.
    + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [AP.expr_vars_lt]. first [apply Nat.ltb_lt | apply N.ltb_lt]. lia.
    + exact Hrest.
    + intros x Hx Hnot. destruct (bv_eq_dec 5 x rb) as [->|NE].
      * rewrite getr_same by exact Hrb0. reflexivity.
      * rewrite getr_other by exact NE. apply Hout; [exact Hx|]. intros [X|X]; [|exact (Hnot X)].
        apply NE. apply ridx_inj. rewrite Hrb, X. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_exit_sound : forall cs E R FULL model TT exitpc rs k' regs' MR',
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  Forall (fun r => 0 < r < 32)%nat rs ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (M_of E cs model FULL) (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 exitpc) MR' (seg_rom SEGS)) ->
  (forall r : bv 5, r <> 0%bv -> ~ In (ridx r) rs -> getr regs' r = getr R r) ->
  know_ok SEGS E MR' k' -> AP.kn_vars_lt (nxt cs) k' = true ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
      cs_ok SEGS A LIMIT SINV argH FS0 E' (PGN.region_exit cs exitpc rs k') R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg_of SEGS R' exitpc FULL' model') TT) ->
  srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) TT.
Proof.
  intros cs E R FULL model TT exitpc rs k' regs' MR' HC Hfresh Hrs Hms Hout HK' Hkv Hk.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_list E (nxt cs) (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) rs)).
  assert (Hag : env_agree (nxt cs) E E') by (unfold E'; apply ext_list_agree).
  unfold PGN.region_exit in Hk.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E' R FULL model TT exitpc (sr_fresh (s_regs (a_ss cs)) rs (nxt cs)) k' ((nxt cs) + N.of_nat (length rs))%N regs' MR'
            HC Hfresh Hag Hms).
  - unfold E'. apply (regs_ok_region rs E (s_regs (a_ss cs)) R regs' (nxt cs) (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hrs Hout).
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma rounddown8_inside : forall SB0 B N x,
  SB0 mod 8 = 0 -> B mod 64 = 0 -> N mod 64 = 0 -> 0 <= B -> B <= x -> x <= B + N - 1 ->
  SB0 + B / 8 <= (SB0 + x / 8) / 8 * 8 /\ (SB0 + x / 8) / 8 * 8 + 8 <= SB0 + B / 8 + N / 8.
Proof. intros. lia. Qed.
Lemma mod64_ge : forall N, N mod 64 = 0 -> 0 < N -> 64 <= N.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_isrc_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_isrc SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold PGN.node_isrc in Hn.
  destruct args as [|eB [|[N| | | | | | | ] [|]]]; try discriminate.
  destruct (Z.eqb (pc cs) (PGN.ISRC_ENTRY T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (eadd (mkSrl (kn cs) eB 3) (ELit PGN.SB))) as [sb sk] eqn:Hsh.
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 19)) as [s3lo|] eqn:Hs3lo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 19)) as [s3hi|] eqn:Hs3hi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond L4]. apply andb_prop in Hcond as [Hcond L3]. apply andb_prop in Hcond as [Hcond L2]. apply andb_prop in Hcond as [Hcond L1].
  apply andb_prop in Hcond as [Hcond Hshi']. apply andb_prop in Hcond as [Hcond Hs3hi']. apply andb_prop in Hcond as [Hcond Hs3lo'].
  apply andb_prop in Hcond as [Hcond HflB]. apply andb_prop in Hcond as [Hcond HN40]. apply andb_prop in Hcond as [Hcond HN0].
  apply andb_prop in Hcond as [Hal HN64].
  apply Z.leb_le in Hal. apply Z.eqb_eq in HN64. apply Z.ltb_lt in HN0. apply Z.ltb_lt in HN40. apply Z.leb_le in Hs3lo'.
  apply Z.ltb_lt in Hs3hi'. apply Z.ltb_lt in Hshi'. apply Z.leb_le in B1. apply Z.leb_le in B2. unfold two64 in Hs3hi', Hshi'.
  injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 19 HC ltac:(lia)) as R19.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Bshi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hs3lo) as Bs3lo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hs3hi) as Bs3hi.
  set (srcw := edenot E (reg cs 11)) in *. set (s3w := edenot E (reg cs 19)) in *.
  set (src := bv_unsigned srcw) in *. set (s3v := bv_unsigned s3w) in *.
  pose proof (u64_range srcw) as Hsr. fold src in Hsr. pose proof (u64_range s3w) as H3r. fold s3v in H3r.
  assert (HsrcW : Z_to_bv 64 src = srcw) by (apply Z_to_bv_bv_unsigned).
  assert (Hs3W : Z_to_bv 64 s3v = s3w) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  set (uB := bv_unsigned (edenot E eB)) in *.
  destruct (flat_x_sound SEGS E M (kn cs) eB 0 (ELit N) HKN HflB) as (FB1 & FB2 & _).
  unfold estart in FB1, FB2. cbn [a_base a_off edenot] in FB1, FB2. fold uB in FB1, FB2. rewrite u64_lit in FB2 by lia.
  destruct (ealign_sound SEGS E M (kn cs) eB HKN) as [_ HeaB]. fold uB in HeaB.
  assert (HB64 : uB mod 64 = 0).
  { destruct HeaB as [q Hq]. rewrite Hq. replace (ealign (kn cs) eB) with ((ealign (kn cs) eB - 6) + 6) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L1) as G1. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L2) as G2.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L3) as G3. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L4) as G4.
  cbn [xt_den] in G1, G2, G3, G4. fold srcw s3w uB src s3v in G1, G2, G3, G4. fold uB in G1, G2, G3, G4. fold src in G1, G2. fold s3v in G3, G4.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ sb sk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) eB 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E eB) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold uB in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk (ELit (N / 8)) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H0 := estart E (SA sb sk)) in *.
  change (bv_unsigned (edenot E sb) + sk) with H0 in Hsa.
  assert (HN8 : 0 <= N / 8 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (HB8 : 0 <= uB / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (mod64_ge N HN64 HN0) as HN64'.
  assert (HN8' : 8 <= N / 8) by (apply Z.div_le_lower_bound; lia).
  replace (elenZ E (ELit (N / 8))) with (N / 8) in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (HH : H0 = RPN.SB + uB / 8).
  { apply (f_equal bv_unsigned) in Hsa. rewrite !u_lit64 in Hsa. unfold two64 in Hsa. unfold PGN.SB, RPN.SB in *.
    change (2147450880 mod 2 ^ 64) with 2147450880 in Hsa.
    rewrite (Z.mod_small (uB / 8)) in Hsa by lia.
    rewrite (Z.mod_small (uB / 8 + 2147450880)) in Hsa by lia. rewrite (Z.mod_small H0) in Hsa by lia. lia. }
  assert (Hz1 : forall j, 0 <= j < 8 -> M (Z_to_bv 64 ((RPN.SB + src / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj.
    pose proof (rounddown8_inside RPN.SB uB N src ltac:(reflexivity) HB64 HN64 ltac:(lia) ltac:(lia) ltac:(lia)) as [X1 X2].
    replace ((RPN.SB + src / 8) / 8 * 8 + j) with (H0 + (((RPN.SB + src / 8) / 8 * 8 - H0) + j)) by lia.
    apply Zb. lia. }
  assert (Hz2 : forall j, 0 <= j < 8 -> M (Z_to_bv 64 ((RPN.SB + (s3v - 1) / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj.
    pose proof (rounddown8_inside RPN.SB uB N (s3v - 1) ltac:(reflexivity) HB64 HN64 ltac:(lia) ltac:(lia) ltac:(lia)) as [X1 X2].
    replace ((RPN.SB + (s3v - 1) / 8) / 8 * 8 + j) with (H0 + (((RPN.SB + (s3v - 1) / 8) / 8 * 8 - H0) + j)) by lia.
    apply Zb. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (ISPEC M (seg_rom SEGS) src s3v R ltac:(lia) ltac:(lia) C1 C2 Hz1 Hz2
              ltac:(rewrite HsrcW; exact R11) ltac:(rewrite Hs3W; exact R19)) as (regs' & Hms & Hout).
  eapply (region_exit_sound cs E R FULL model TT (PGN.ISRC_EXIT T) PGN.ISRC_REGS (kn cs) regs' M HC Hfresh).
  - unfold PGN.ISRC_REGS. repeat constructor.
  - rewrite Hpc. exact Hms.
  - intros r Hr0 Hnot. unfold PGN.ISRC_REGS in Hnot.
    apply Hout; intros ->; apply Hnot; cbv; auto 10.
  - exact HKN.
  - destruct (w_fresh_ok_parts nx0 cs Hfresh) as (_ & Fkn & _). exact Fkn.
  - intros E' R' FULL' model' Hag HC' Hfs'. apply (Hk E' R' FULL' model' Hag HC' Hfs').
Qed.

(* [comment removed for export] *)
Lemma rdn8_of_bytes : forall M (a : Z),
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists bt, rdn SEGS M (Z_to_bv 64 (a + i)) 1 = Some [bt]) ->
  exists bs, rdn SEGS M (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros M a Ha0 Ha8 Hb.
  assert (GEN : forall (m : nat) (c : Z), a <= c -> c + Z.of_nat m <= a + 8 ->
             exists bs, rdn SEGS M (Z_to_bv 64 c) m = Some bs).
  { induction m as [|m IH]; intros c Hc1 Hc2; [exists []; reflexivity|].
    destruct (Hb (c - a)) as [bt Hbt]; [lia|]. replace (a + (c - a)) with c in Hbt by lia.
    destruct (IH (c + 1)) as [bs Hbs]; [lia | lia |].
    exists (bt :: bs). apply rdn_cons1; [exact Hbt|]. rewrite zbv_add1. exact Hbs. }
  destruct (GEN 8%nat a) as [bs Hbs]; [lia | cbn; lia |]. exists bs. exact Hbs.
Qed.

(* [comment removed for export] *)
Lemma sh_split_estart : forall E M k b hb hk m,
  know_ok SEGS E M k -> split_lit (eadd (mkSrl k b 3) (ELit RPN.SB)) = (hb, hk) ->
  0 <= estart E (SA hb hk) -> estart E (SA hb hk) + m <= 2 ^ 64 -> 0 < m ->
  estart E (SA hb hk) = RPN.SB + bv_unsigned (edenot E b) / 8.
Proof.
  intros E M k b hb hk m HK Hs G0 G1 Gm. pose proof (u64_range (edenot E b)) as Rb.
  rewrite (estart_of_split E _ hb hk m Hs G0 G1 Gm).
  unfold eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64. rewrite (u_srl3 SEGS E M k b HK).
  rewrite u64_lit. unfold two64, RPN.SB.
  assert (0 <= bv_unsigned (edenot E b) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small by lia. lia.
  all: unfold RPN.SB; lia.
Qed.

Lemma zero_diff_sound : forall E M k a b,
  know_ok SEGS E M k -> PGN.zero_diff k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold PGN.zero_diff, PGV.zero_diff in H.
  destruct (erange k (mkAlu ALU_SUB a b)) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k _ 0 0 HK Her) as Hz. rewrite mkAlu_denot in Hz. cbn [edenot] in Hz.
  rewrite u_sub64 in Hz. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  apply mod64_diff_zero; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land7_mod : forall z, 0 <= z -> Z.land z 7 = z mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma pg_arith : forall m, 0 <= m < 8 -> m <> 0 -> (m + 250 * (if m <? 1 then 1 else 0)) mod 2 ^ 64 = m.
Proof. intros m Hm H0. replace (m <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.mod_small; lia. Qed.
Lemma rd8_window : forall H0 n, 0 <= H0 -> H0 mod 8 = 0 \/ True -> 1 <= n <= 64 ->
  forall hb8 : Z, hb8 mod 8 = 0 -> exists d, H0 = hb8 + d /\ True.
Proof. intros. exists (H0 - hb8). lia. Qed.
Lemma rd8_facts : forall ub hk p n, ub mod 8 = 0 -> 0 <= ub -> RPN.SB + p / 8 = ub + hk -> p mod 8 = 0 -> 0 <= p -> 1 <= n <= 64 ->
  (RPN.SB + p / 8) / 8 * 8 = ub + (hk - hk mod 8)
  /\ ub + (hk - hk mod 8) <= (RPN.SB + (p + n - 1) / 8) / 8 * 8
  /\ (RPN.SB + (p + n - 1) / 8) / 8 * 8 + 8 <= ub + (hk - hk mod 8) + 16.
Proof. intros. unfold RPN.SB in *. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pgsel_arith : forall m x, 0 <= m < 8 -> 0 <= x < 2 ^ 64 ->
  (m + ((if m <? 1 then 1 else 0) * x) mod 2 ^ 64) mod 2 ^ 64 = (if m =? 0 then x else m).
Proof.
  intros m x Hm Hx. destruct (Z.eqb_spec m 0) as [->|NE].
  - cbn [Z.ltb]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace (m <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.mul_0_l, (Z.mod_small 0) by lia.
    rewrite Z.mod_small; lia.
Qed.
Lemma q_range : forall n nhi, 1 <= n <= nhi -> 0 <= n / 8 <= nhi / 8 /\ nhi / 8 < 2 ^ 61 - 1 \/ nhi >= 2 ^ 64 - 8.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Theorem node_idst_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_idst SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold PGN.node_idst in Hn. destruct args; [|discriminate].
  destruct (Z.eqb (pc cs) (PGN.IDST_ENTRY T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  unfold PGN.idst_tests in Hn. change PGN.SB with RPN.SB in Hn.
  destruct (split_lit (eadd (mkSrl (kn cs) (reg cs 10) 3) (ELit RPN.SB))) as [hb hk] eqn:Hsh.
  destruct (split_lit (eadd (eadd (mkSrl (kn cs) (reg cs 10) 3) (ELit RPN.SB)) (mkSrl (kn cs) (reg cs 12) 3))) as [pb pk] eqn:Hsp.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Htests; [|discriminate] end.
  injection Hn as <-. cbn [forallb] in Htests.
  apply andb_prop in Htests as [Hal Htests]. apply andb_prop in Htests as [Hn1 Htests]. apply andb_prop in Htests as [Hn64 Htests].
  apply andb_prop in Htests as [Hd47 Htests]. apply andb_prop in Htests as [Hfld Htests].
  apply andb_prop in Htests as [L1 Htests]. apply andb_prop in Htests as [L2 Htests].
  apply andb_prop in Htests as [Tz Htests]. apply andb_prop in Htests as [Tp Htests].
  apply andb_prop in Htests as [Halh Htests]. apply andb_prop in Htests as [Trw Htests].
  apply andb_prop in Htests as [B1 Htests]. apply andb_prop in Htests as [B2 Htests].
  apply andb_prop in Htests as [Igsb Htests]. apply andb_prop in Htests as [Lsb Htests]. apply andb_prop in Htests as [Hfresh _].
  apply Z.leb_le in Hal. apply Z.leb_le in Hn1. apply Z.leb_le in Hn64. apply Z.ltb_lt in Hd47. apply Z.leb_le in Halh.
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 20 HC ltac:(lia)) as R20.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Bnlo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Bnhi.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Bdhi.
  set (dw := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (s4w := edenot E (reg cs 20)) in *.
  set (p := bv_unsigned dw) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range dw) as Hpr. fold p in Hpr. pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (HdwP : Z_to_bv 64 p = dw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L1) as G1. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN L2) as G2.
  cbn [xt_den] in G1, G2. fold dw nw s4w in G1, G2. fold p n in G1, G2.
  assert (Hs4 : bv_unsigned s4w = p + n) by lia.
  assert (Hs4W : Z_to_bv 64 (p + n) = s4w) by (rewrite <- Hs4; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) (reg cs 10) HKN) as [_ Hea]. fold dw in Hea.
  assert (Hp8 : p mod 8 = 0).
  { unfold p. destruct Hea as [qq Hq]. rewrite Hq. replace (ealign (kn cs) (reg cs 10)) with ((ealign (kn cs) (reg cs 10) - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (Hp8r : 0 <= p / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (* [comment removed for export] *)
  destruct (rw_lit_sound SEGS SEGS_wr E M (kn cs) hb (hk - hk mod 8) 16 HKN ltac:(lia) Trw) as (_ & _ & RD16 & W0 & W16).
  destruct (ealign_sound SEGS E M (kn cs) hb HKN) as [_ Heah].
  set (ub := bv_unsigned (edenot E hb)) in *.
  assert (Hub8 : ub mod 8 = 0).
  { destruct Heah as [qq Hq]. rewrite Hq. replace (ealign (kn cs) hb) with ((ealign (kn cs) hb - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  pose proof (Z.mod_pos_bound hk 8 ltac:(lia)) as Hm8.
  unfold estart in W0, W16, RD16. cbn [a_base a_off] in W0, W16, RD16. fold ub in W0, W16, RD16.
  assert (HH0 : estart E (SA hb hk) = RPN.SB + p / 8).
  { apply (sh_split_estart E M (kn cs) (reg cs 10) hb hk 1 HKN Hsh); unfold estart; cbn [a_base a_off]; fold ub; lia. }
  unfold estart in HH0. cbn [a_base a_off] in HH0. fold ub in HH0.
  pose proof (u64_range (edenot E hb)) as Rub. fold ub in Rub.
  destruct (rd8_facts ub hk p n Hub8 ltac:(lia) ltac:(lia) Hp8 ltac:(lia) ltac:(lia)) as (RF1 & RF2 & RF3).
  destruct (rdn8_of_bytes M ((RPN.SB + p / 8) / 8 * 8)) as [bs1 Hw1]; [lia | lia | |].
  { intros i Hi. rewrite RF1. replace (ub + (hk - hk mod 8) + i) with (ub + (hk - hk mod 8) + i) by lia. apply RD16. lia. }
  destruct (rdn8_of_bytes M ((RPN.SB + (p + n - 1) / 8) / 8 * 8)) as [bs2 Hw2]; [lia | lia | |].
  { intros i Hi. replace ((RPN.SB + (p + n - 1) / 8) / 8 * 8 + i) with (ub + (hk - hk mod 8) + (((RPN.SB + (p + n - 1) / 8) / 8 * 8 - (ub + (hk - hk mod 8))) + i)) by lia.
    apply RD16. lia. }
  (* [comment removed for export] *)
  assert (Hzero : forall i, 0 <= i < n / 8 -> M (Z_to_bv 64 (RPN.SB + p / 8 + i)) = Some (Z_to_bv 8 0)).
  { apply Bool.orb_prop in Tz. destruct Tz as [Tlt | Tz].
    - apply Z.ltb_lt in Tlt. intros i Hi. exfalso.
      assert (n / 8 = 0) by (apply Z.div_small; lia). lia.
    - apply andb_prop in Tz as [Tfl Tkz].
      destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (mkSrl (kn cs) (reg cs 12) 3) HKN HKN Tkz) as (Zb & _ & _).
      unfold elenZ in Zb. rewrite (u_srl3 SEGS E M (kn cs) (reg cs 12) HKN) in Zb. fold nw n in Zb.
      intros i Hi. unfold estart in Zb. cbn [a_base a_off] in Zb. fold ub in Zb. rewrite <- HH0. apply Zb. exact Hi. }
  (* [comment removed for export] *)
  assert (Hlast : exists b1 : byte, n mod 8 <> 0 ->
            rdn SEGS M (Z_to_bv 64 (RPN.SB + p / 8 + n / 8)) 1 = Some [b1] /\ n mod 8 <= bv_unsigned b1 <= 127).
  { assert (CASES : n mod 8 = 0 \/
             (flat_x (kn cs) pb pk (ELit 1) &&
              match know_lookup SEGS (kn cs) pb pk 1 false [] [] with
              | LHit v sc _ => match sc with [] => PGN.partial_val_ok (kn cs) (reg cs 12) v | _ :: _ => false end
              | _ => false
              end)%bool = true).
    { destruct (lowbits (kn cs) (reg cs 12) 3) as [[|lbp|lbn]|] eqn:Hlb; [left | right; exact Tp | right; exact Tp | right; exact Tp].
      pose proof (lowbits_sound SEGS E M (kn cs) (reg cs 12) 3 0 HKN ltac:(lia) Hlb) as X. fold nw n in X. exact X. }
    clear Tp. destruct CASES as [Hr0 | Tp].
    - exists (Z_to_bv 8 0). intros Hr. exfalso. exact (Hr Hr0).
    - apply andb_prop in Tp as [Pfl Tp].
      destruct (know_lookup SEGS (kn cs) pb pk 1 false [] []) as [v sc hs|sc hs|] eqn:HL; try discriminate.
      destruct sc; [|discriminate].
      destruct (flat_x_sound SEGS E M (kn cs) pb pk (ELit 1) HKN Pfl) as (Plo & Phi & _).
      cbn [edenot] in Phi. rewrite u64_lit in Phi by lia.
      destruct (lookup_piece SEGS E M (kn cs) pb pk 1 v hs HKN ltac:(lia) HL ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
      pose proof (estart_of_split E _ pb pk 1 Hsp Plo Phi ltac:(lia)) as Epb.
      assert (Eaddr : estart E (SA pb pk) = RPN.SB + p / 8 + n / 8).
      { rewrite Epb. unfold eadd at 1. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64.
        rewrite (u_srl3 SEGS E M (kn cs) (reg cs 12) HKN). fold nw n.
        pose proof (w_split_lit_denot E _ hb hk Hsh) as D. apply (f_equal bv_unsigned) in D. rewrite u_lit64 in D. unfold two64 in D.
        fold ub in D. rewrite (Z.mod_small (ub + hk)) in D by lia. rewrite D. rewrite <- HH0.
        assert (0 <= n / 8 <= 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
        apply Z.mod_small. lia. }
      exists (Z_to_bv 8 (bv_unsigned (edenot E v))). intros Hr. split.
      + rewrite <- Eaddr. rewrite <- Hbs, w2b1 in Hrd. exact Hrd.
      + (* [comment removed for export] *)
        pose proof (u64_range (edenot E v)) as Rv. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M8.
        assert (Hv : bv_unsigned (edenot E v) = n mod 8).
        { unfold n, nw. apply (partial_val_ok_sound SEGS E M (kn cs)); [exact HKN | exact Tp | fold nw n; exact Hr]. }
        rewrite Hv. rewrite (RefEnframeArith.u8_lit (n mod 8)) by lia. lia. }
  destruct Hlast as [b1 Hlast].
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (DSPEC M (seg_rom SEGS) p n b1 bs1 bs2 R ltac:(lia) Hp8 ltac:(lia) ltac:(lia) C1 C2 Hzero Hlast Hw1 Hw2
              ltac:(rewrite HdwP; exact R10) ltac:(rewrite Hs4W; exact R20)) as (regs' & Hms & Hout).
  eapply (region_exit_sound cs E R FULL model TT (PGN.IDST_EXIT T) PGN.IDST_REGS (kn cs) regs' M HC Hfresh).
  - unfold PGN.IDST_REGS. repeat constructor.
  - rewrite Hpc. exact Hms.
  - intros x Hx0 Hnot. unfold PGN.IDST_REGS in Hnot.
    apply Hout; intros ->; apply Hnot; cbv; auto 10.
  - exact HKN.
  - destruct (w_fresh_ok_parts nx0 cs Hfresh) as (_ & Fkn & _). exact Fkn.
  - intros E' R' FULL' model' Hag HC' Hfs'. apply (Hk E' R' FULL' model' Hag HC' Hfs').
Qed.

(* [comment removed for export] *)
Hypothesis IMG_gfl : img_cell SEGS (RPN.rp_gfl T) (RPN.rp_cfl T).

Theorem node_pgran_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_pgran SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  rewrite PGN.node_pgran_eq in Hn. unfold PGN.node_pgran_ref in Hn. destruct args; [|discriminate].   (* [comment removed for export] *)
  destruct (Z.eqb (pc cs) (PGN.PG_ENTRY T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  unfold PGN.pg_tests in Hn. change PGN.SB with RPN.SB in Hn.
  destruct (split_lit (eadd (mkSrl (kn cs) (reg cs 20) 3) (ELit RPN.SB))) as [hb hk] eqn:Hsh.
  destruct (split_lit (eadd (eadd (mkSrl (kn cs) (reg cs 20) 3) (ELit RPN.SB)) (mkSrl (kn cs) (reg cs 9) 3))) as [pb pk] eqn:Hsp.
  destruct (xlo (kn cs) (reg cs 9)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 9)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 20)) as [plo|] eqn:Hplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 20)) as [phi|] eqn:Hphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Htests; [|discriminate] end.
  injection Hn as <-. cbn [forallb] in Htests.
  apply andb_prop in Htests as [Zs6 Htests]. apply andb_prop in Htests as [Pfl Htests]. apply andb_prop in Htests as [Kvl Htests].
  apply andb_prop in Htests as [Pvl Htests].
  apply andb_prop in Htests as [Hn1 Htests]. apply andb_prop in Htests as [Hal Htests].
  apply andb_prop in Htests as [Hplo' Htests]. apply andb_prop in Htests as [Hphi' Htests].
  apply andb_prop in Htests as [P1 Htests]. apply andb_prop in Htests as [P2 Htests]. apply andb_prop in Htests as [P3 Htests].
  apply andb_prop in Htests as [P4 Htests]. apply andb_prop in Htests as [P5 Htests]. apply andb_prop in Htests as [P6 Htests].
  apply andb_prop in Htests as [P7 Htests]. apply andb_prop in Htests as [P8 Htests]. apply andb_prop in Htests as [P9 Htests].
  apply andb_prop in Htests as [Igsb Htests]. apply andb_prop in Htests as [Igm1 Htests]. apply andb_prop in Htests as [Igm2 Htests].
  apply andb_prop in Htests as [Ighi Htests]. apply andb_prop in Htests as [Icm1 Htests]. apply andb_prop in Htests as [Icm2 Htests].
  apply andb_prop in Htests as [Igfl Htests].
  apply andb_prop in Htests as [Lsb Htests]. apply andb_prop in Htests as [Lhi Htests].
  apply andb_prop in Htests as [Cpp Htests]. apply andb_prop in Htests as [Ccp Htests].
  apply andb_prop in Htests as [Hwr Htests]. apply andb_prop in Htests as [Hflh Htests]. apply andb_prop in Htests as [Hfresh _].
  apply Z.leb_le in Hn1. apply Z.leb_le in Hal. apply Z.leb_le in Hphi'.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5.
  apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8. apply Z.leb_le in P9.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 20 HC ltac:(lia)) as R20.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 22 HC ltac:(lia)) as R22.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Bnlo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Bnhi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hplo) as Bplo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hphi) as Bphi.
  set (nw := edenot E (reg cs 9)) in *. set (pw := edenot E (reg cs 20)) in *. set (s6w := edenot E (reg cs 22)) in *.
  set (n := bv_unsigned nw) in *. set (p := bv_unsigned pw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range pw) as Hpr. fold p in Hpr.
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HpwP : Z_to_bv 64 p = pw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (BAND : p + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= p /\ p + n <= RPN.kHighEnd)).
  { apply orb_prop in Hplo' as [Hx|Hx].
    - apply andb_prop in Hx as [Hx1 Hx2]. apply Z.leb_le in Hx1. apply Z.leb_le in Hx2. right. lia.
    - pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (reg cs 20) 0 (reg cs 9) HC Hx) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off] in OB. rewrite Z.add_0_r in OB. fold pw nw in OB. fold p n in OB.
      specialize (OB ltac:(lia)). unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd, LOWTOP, KHI, TOPMAX, STK in *. lia. }
  assert (Hphi'' : p + n <= 0x7fffffffffff) by (unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in BAND; lia).
  (* [comment removed for export] *)
  pose proof (zero_diff_sound E M (kn cs) _ _ HKN Zs6) as X6. cbn [edenot] in X6. rewrite u_mul64 in X6.
  rewrite (u_srl3 SEGS E M (kn cs) (reg cs 9) HKN) in X6. fold nw n s6w in X6. rewrite (u64_lit 8) in X6 by lia.
  assert (Hq : 0 <= n / 8 <= n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite Z.mod_small in X6 by lia.
  assert (Hs6W : Z_to_bv 64 (8 * (n / 8)) = s6w) by (rewrite <- X6; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) (reg cs 20) HKN) as [_ Hea]. fold pw in Hea.
  assert (Hp8 : p mod 8 = 0).
  { unfold p. destruct Hea as [qq Hqq]. rewrite Hqq. replace (ealign (kn cs) (reg cs 20)) with ((ealign (kn cs) (reg cs 20) - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN P2 Lsb) as C2.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN P8 Lhi) as C8.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igfl IMG_gfl) as C9.
  destruct (cell_is_sound SEGS E M (kn cs) (ELit 0) (RPN.rp_cfl T + 85) 1 1 HKN ltac:(lia) Cpp) as (Dpp & _ & _).
  destruct (cell_is_sound SEGS E M (kn cs) (ELit 0) (RPN.rp_ccp T) 1 1 HKN ltac:(lia) Ccp) as (Dcp & _ & _).
  rewrite estart_lit0 in Dpp, Dcp.
  change (word_to_le_bytes 1 (Z_to_bv 64 1)) with [Z_to_bv 8 1] in Dpp, Dcp.
  (* [comment removed for export] *)
  assert (Hn8 : 0 <= n / 8) by (apply Z.div_pos; lia).
  assert (Hlen : elenZ E (eaddz (mkSrl (kn cs) (reg cs 9) 3) 1) = n / 8 + 1).
  { unfold elenZ, eaddz, eadd. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64, (u_srl3 SEGS E M (kn cs) (reg cs 9) HKN).
    fold nw. fold n. rewrite !u64_lit by lia. unfold two64. rewrite Z.mod_small; [reflexivity | lia]. }
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) hb hk (eaddz (mkSrl (kn cs) (reg cs 9) 3) 1) HKN HKN Hwr) as (WstF & W0 & W1).
  rewrite Hlen in WstF, W1.
  pose proof (WstF (Z.to_nat (n / 8 + 1)) ltac:(lia)) as Wst.
  assert (HH0 : estart E (SA hb hk) = RPN.SB + p / 8).
  { apply (sh_split_estart E M (kn cs) (reg cs 20) hb hk (n / 8 + 1) HKN Hsh W0 W1). lia. }
  rewrite HH0 in Wst, W0, W1.
  set (sa := RPN.SB + p / 8 + n / 8) in *.
  assert (Hsa : 0 <= sa /\ sa + 1 <= 2 ^ 64) by (unfold sa; lia).
  assert (Hst : store_ok SEGS M (Z_to_bv 64 sa) 1 = true).
  { apply store_ok_of_all; [rewrite u64_lit by lia; cbn; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. cbn in Hx.
    apply (store_ok_all SEGS M (Z.to_nat (n / 8 + 1)) (Z_to_bv 64 (RPN.SB + p / 8)) ltac:(rewrite u64_lit by lia; lia) Wst).
    rewrite u64_lit by lia. unfold sa in Hx. lia. }
  (* [comment removed for export] *)
  destruct (flat_x_sound SEGS E M (kn cs) pb pk (ELit 1) HKN Pfl) as (Plo & Phi & _).
  cbn [edenot] in Phi. rewrite u64_lit in Phi by lia.
  assert (Eaddr : estart E (SA pb pk) = sa).
  { rewrite (estart_of_split E _ pb pk 1 Hsp Plo Phi ltac:(lia)). unfold eadd at 1. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64.
    rewrite (u_srl3 SEGS E M (kn cs) (reg cs 9) HKN). fold nw n.
    pose proof (w_split_lit_denot E _ hb hk Hsh) as D. apply (f_equal bv_unsigned) in D. rewrite u_lit64 in D. unfold two64 in D.
    unfold estart in HH0. cbn [a_base a_off] in HH0.
    rewrite (Z.mod_small _) in D by (pose proof (u64_range (edenot E hb)); lia). rewrite D, HH0. unfold sa. apply Z.mod_small. lia. }
  (* [comment removed for export] *)
  destruct (PSPEC M (seg_rom SEGS) p n R ltac:(lia) Hp8 ltac:(lia) BAND
              C1 C2 C3 C4 C5 C6 C7 C8 C9 Dpp Dcp Hst
              ltac:(rewrite HnwN; exact R9) ltac:(rewrite Hs6W; exact R22) ltac:(rewrite HpwP; exact R20)) as (regs' & Hms & Hout).
  fold sa in Hms.
  set (MR' := if (n mod 8 =? 0)%Z then M else wbytes M (Z_to_bv 64 sa) (word_to_le_bytes 1 (Z_to_bv 64 (n mod 8)))) in Hms.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M8.
  (* [comment removed for export] *)
  assert (Hsame : forall x : word, bv_unsigned x < sa \/ sa + 1 <= bv_unsigned x -> MR' x = M x).
  { intros x Hx. unfold MR'. destruct (n mod 8 =? 0)%Z; [reflexivity|].
    apply wbytes_same_far; rewrite w2b1; cbn [length]; rewrite u64_lit by lia; lia. }
  assert (Hgrows : mem_grows M MR').
  { unfold MR'. destruct (n mod 8 =? 0)%Z; [apply mem_grows_refl | apply wbytes_grows]. }
  (* [comment removed for export] *)
  assert (exists b : byte, rdn SEGS MR' (Z_to_bv 64 sa) 1 = Some [b] /\
                           (n mod 8 <> 0 -> bv_unsigned b = n mod 8)) as (b & HbM & Hbv).
  { unfold MR'. destruct (Z.eqb_spec (n mod 8) 0) as [R0|R1].
    - destruct (store_ok_readable SEGS SEGS_wr M sa 1 ltac:(lia) ltac:(cbn; lia) Hst 0 ltac:(cbn; lia)) as [bt Hbt].
      rewrite Z.add_0_r in Hbt. exists bt. split; [exact Hbt | intros X; exfalso; exact (X R0)].
    - exists (Z_to_bv 8 (n mod 8)). split.
      + rewrite w2b1. rewrite (u64_lit (n mod 8)) by lia.
        apply (rdn_wbytes_hit SEGS [Z_to_bv 8 (n mod 8)] M). cbn [length]. rewrite u64_lit by lia. lia.
      + intros _. rewrite RefEnframeArith.u8_lit by lia. reflexivity. }
  pose proof (u8_range b) as Hb8.
  (* [comment removed for export] *)
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E1 := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned b))).
  set (E' := ext_list E1 (N.succ (nxt cs)) (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) PGN.PG_REGS)).
  assert (Hag1 : env_agree (nxt cs) E E1) by (unfold E1; apply ext1_agree).
  assert (Hag2 : env_agree (N.succ (nxt cs)) E1 E') by (unfold E'; apply ext_list_agree).
  assert (Hag : env_agree (nxt cs) E E').
  { eapply env_agree_trans; [exact Hag1|]. eapply env_agree_le; [exact Hag2 | lia]. }
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E' R FULL model TT (PGN.PG_EXIT T) (sr_fresh (s_regs (a_ss cs)) PGN.PG_REGS (N.succ (nxt cs)))
            (KWord (SA pb pk) 1 (PGN.pgsel (reg cs 9) (EVar (nxt cs))) :: kn_havoc_led (kn cs) (a_maps cs) pb pk (ELit 1))
            (N.succ (nxt cs) + N.of_nat (length PGN.PG_REGS))%N regs' MR'
            HC Hfresh Hag).
  - rewrite Hpc. exact Hms.
  - unfold E'. apply (regs_ok_region PGN.PG_REGS E1 (s_regs (a_ss cs)) R regs' (N.succ (nxt cs))).
    + eapply regs_ok_agree'; [exact Hag1 | exact Fsr | exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC)].
    + eapply sr_vars_lt_mono; [exact Fsr | lia].
    + unfold PGN.PG_REGS. repeat constructor.
    + intros x Hx0 Hnot. unfold PGN.PG_REGS in Hnot. apply Hout; intros ->; apply Hnot; cbv; auto 12.
  - (* [comment removed for export] *)
    constructor.
    + (* [comment removed for export] *)
      cbn [kentry_ok].
      assert (Epb : estart E' (SA pb pk) = sa).
      { rewrite <- Eaddr. unfold estart. cbn [a_base a_off]. f_equal. f_equal. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag | exact Pvl]. }
      split; [lia|]. split; [unfold flat; rewrite Epb; lia|].
      assert (Had : adenot E' (SA pb pk) = Z_to_bv 64 sa).
      { unfold adenot, v_addi. cbn [a_base a_off]. fold (estart E' (SA pb pk)). unfold estart in Epb. cbn [a_base a_off] in Epb.
        rewrite Epb. reflexivity. }
      rewrite Had, HbM. f_equal. rewrite w2b1. f_equal.
      (* [comment removed for export] *)
      assert (Ene : edenot E' (reg cs 9) = nw).
      { unfold nw. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
      assert (EX : ev E' (nxt cs) = Z_to_bv 64 (bv_unsigned b)).
      { destruct Hag2 as [Hv2 _]. rewrite <- (Hv2 (nxt cs)) by lia. unfold E1. apply ext1_at. }
      unfold PGN.pgsel, PGV.pgsel. cbn [edenot]. rewrite Ene, EX.
      rewrite u_add64, u_and64, u_mul64, u_sltu64, u_and64. fold n. rewrite !(u64_lit 7) by lia. rewrite (u64_lit 1) by lia.
      rewrite (u64_lit (bv_unsigned b)) by lia. rewrite land7_mod by lia. rewrite pgsel_arith by lia.
      destruct (Z.eqb_spec (n mod 8) 0) as [R0|R1]; [symmetry; apply Z_to_bv_bv_unsigned|].
      rewrite <- (Hbv R1). symmetry. apply Z_to_bv_bv_unsigned.
    + eapply know_ok_agree'; [exact Hag | exact Kvl |].
      eapply w_know_ok_havoc_led; [exact HKN | | exact Hgrows |].   (* [comment removed for export] *)
      * intros x Hx. apply Hsame. rewrite Eaddr in Hx. unfold elenZ in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia. exact Hx.
      * intros m m' Hm Hm' Hf Hf' Hne. exact (w_maps_match_disjoint0 E (a_maps cs) _ m m' (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hm' Hf Hf' Hne).
  - intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Theorem node_rppart_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_rppart SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold PGN.node_rppart in Hn. destruct args; [|discriminate].
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  unfold PGN.rpp_tests in Hn. change PGN.SB with RPN.SB in Hn.
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (split_lit (eadd (mkSrl (kn cs) (reg cs 10) 3) (ELit RPN.SB))) as [hb hk] eqn:Hsh.
  destruct (split_lit (eadd (eadd (mkSrl (kn cs) (reg cs 10) 3) (ELit RPN.SB)) (mkSrl (kn cs) (reg cs 11) 3))) as [pb pk] eqn:Hsp.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Htests; [|discriminate] end.
  cbn [forallb] in Htests.
  apply andb_prop in Htests as [Hn16 Htests]. apply andb_prop in Htests as [Hn40 Htests]. apply andb_prop in Htests as [Hal Htests].
  apply andb_prop in Htests as [Hblo' Htests]. apply andb_prop in Htests as [Hbhi' Htests].
  apply andb_prop in Htests as [Hsplo' Htests]. apply andb_prop in Htests as [Hsphi' Htests]. apply andb_prop in Htests as [Hdisj Htests].
  apply andb_prop in Htests as [P1 Htests]. apply andb_prop in Htests as [P2 Htests]. apply andb_prop in Htests as [P3 Htests].
  apply andb_prop in Htests as [P4 Htests]. apply andb_prop in Htests as [P5 Htests]. apply andb_prop in Htests as [P6 Htests].
  apply andb_prop in Htests as [P7 Htests]. apply andb_prop in Htests as [P8 Htests].
  apply andb_prop in Htests as [B1 Htests]. apply andb_prop in Htests as [B2 Htests]. apply andb_prop in Htests as [B3 Htests].
  apply andb_prop in Htests as [B4 Htests]. apply andb_prop in Htests as [B5 Htests]. apply andb_prop in Htests as [B6 Htests].
  apply andb_prop in Htests as [B7 Htests]. apply andb_prop in Htests as [B8 Htests].
  apply andb_prop in Htests as [Hwr Htests]. apply andb_prop in Htests as [Hflq Htests].
  apply andb_prop in Htests as [Hflh Htests]. apply andb_prop in Htests as [Hkz Htests]. apply andb_prop in Htests as [Tp Htests].
  apply andb_prop in Htests as [Igsb Htests]. apply andb_prop in Htests as [Igm1 Htests]. apply andb_prop in Htests as [Igm2 Htests].
  apply andb_prop in Htests as [Ighi Htests]. apply andb_prop in Htests as [Icm1 Htests]. apply andb_prop in Htests as [Icm2 Htests].
  apply andb_prop in Htests as [Lsb Htests]. apply andb_prop in Htests as [Lhi _].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hal. apply Z.leb_le in Hbhi'.
  apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj. unfold two64 in Hsphi'.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr.
  (* [comment removed for export] *)
  assert (BAND : beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)).
  { rewrite off_bandL_or in Hblo'. apply orb_prop in Hblo' as [Hx|Hx].
    - apply andb_prop in Hx as [Hx1 Hx2]. apply Z.leb_le in Hx1. apply Z.leb_le in Hx2. right. lia.
    - pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model (reg cs 10) 0 (reg cs 11) HC Hx) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off] in OB. rewrite Z.add_0_r in OB. fold begw nw in OB. fold beg n in OB.
      specialize (OB ltac:(lia)). unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd, LOWTOP, KHI, TOPMAX, STK in *. lia. }
  assert (Hbhi'' : beg + n <= 0x7fffffffffff) by (unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in BAND; lia).
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) (reg cs 10) HKN) as [_ Hea]. fold begw in Hea.
  assert (Hbeg8 : beg mod 8 = 0).
  { unfold beg. destruct Hea as [qq Hqq]. rewrite Hqq. replace (ealign (kn cs) (reg cs 10)) with ((ealign (kn cs) (reg cs 10) - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (mkSrl (kn cs) (reg cs 11) 3) HKN HKN Hkz) as (Zb & Z0 & Z1).
  unfold elenZ in Zb, Z1. rewrite (u_srl3 SEGS E M (kn cs) (reg cs 11) HKN) in Zb, Z1. fold nw n in Zb, Z1.
  assert (Hq2 : 2 <= n / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HH0 : estart E (SA hb hk) = RPN.SB + beg / 8).
  { apply (sh_split_estart E M (kn cs) (reg cs 10) hb hk (n / 8) HKN Hsh Z0 Z1). lia. }
  assert (Hz : forall i, 0 <= i < n / 8 -> M (Z_to_bv 64 (RPN.SB + beg / 8 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite <- HH0. apply Zb. exact Hi. }
  (* [comment removed for export] *)
  assert (Hlast : exists b1 : byte, n mod 8 <> 0 ->
            rdn SEGS M (Z_to_bv 64 (RPN.SB + beg / 8 + n / 8)) 1 = Some [b1] /\ bv_unsigned b1 = n mod 8).
  { assert (CASES : n mod 8 = 0 \/
             (flat_x (kn cs) pb pk (ELit 1) &&
              match know_lookup SEGS (kn cs) pb pk 1 false [] [] with
              | LHit v sc _ => match sc with [] => PGN.partial_val_ok (kn cs) (reg cs 11) v | _ :: _ => false end
              | _ => false
              end)%bool = true).
    { destruct (lowbits (kn cs) (reg cs 11) 3) as [[|lbp|lbn]|] eqn:Hlb; [left | right; exact Tp | right; exact Tp | right; exact Tp].
      pose proof (lowbits_sound SEGS E M (kn cs) (reg cs 11) 3 0 HKN ltac:(lia) Hlb) as X. fold nw n in X. exact X. }
    clear Tp. destruct CASES as [Hr0 | Tp].
    - exists (Z_to_bv 8 0). intros Hr. exfalso. exact (Hr Hr0).
    - apply andb_prop in Tp as [Pfl Tp].
      destruct (know_lookup SEGS (kn cs) pb pk 1 false [] []) as [v sc hs|sc hs|] eqn:HL; try discriminate.
      destruct sc; [|discriminate].
      destruct (flat_x_sound SEGS E M (kn cs) pb pk (ELit 1) HKN Pfl) as (Plo & Phi & _).
      cbn [edenot] in Phi. rewrite u64_lit in Phi by lia.
      destruct (lookup_piece SEGS E M (kn cs) pb pk 1 v hs HKN ltac:(lia) HL ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
      pose proof (estart_of_split E _ pb pk 1 Hsp Plo Phi ltac:(lia)) as Epb.
      assert (Eaddr : estart E (SA pb pk) = RPN.SB + beg / 8 + n / 8).
      { rewrite Epb. unfold eadd at 1. rewrite mkAlu_denot. cbn [edenot]. rewrite u_add64.
        rewrite (u_srl3 SEGS E M (kn cs) (reg cs 11) HKN). fold nw n.
        pose proof (w_split_lit_denot E _ hb hk Hsh) as D. apply (f_equal bv_unsigned) in D. rewrite u_lit64 in D. unfold two64 in D.
        unfold estart in HH0, Z0, Z1. cbn [a_base a_off] in HH0, Z0, Z1.
        rewrite (Z.mod_small _) in D by (pose proof (u64_range (edenot E hb)); lia). rewrite D, HH0.
        assert (n / 8 <= 2 ^ 40 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 40 / 8) with 137438953472 in *.
        assert (beg / 8 <= 140737488355327 / 8) by (apply Z.div_le_mono; lia). change (140737488355327 / 8) with 17592186044415 in *.
        unfold RPN.SB. apply Z.mod_small. pose proof (Z.div_pos beg 8). lia. }
      exists (Z_to_bv 8 (bv_unsigned (edenot E v))). intros Hr. split.
      + rewrite <- Eaddr. rewrite <- Hbs, w2b1 in Hrd. exact Hrd.
      + pose proof (u64_range (edenot E v)) as Rv. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M8.
        assert (Hv : bv_unsigned (edenot E v) = n mod 8).
        { unfold n, nw. apply (partial_val_ok_sound SEGS E M (kn cs)); [exact HKN | exact Tp | fold nw n; exact Hr]. }
        rewrite Hv. rewrite (RefEnframeArith.u8_lit (n mod 8)) by lia. reflexivity. }
  destruct Hlast as [b1 Hlast].
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hdisj2 : RPN.SB + (beg + n - 1) / 8 < usp - 72).
  { assert ((beg + n - 1) / 8 <= (bhi + nhi - 1) / 8) by (apply Z.div_le_mono; lia). unfold RPN.SB. unfold PGN.SB, RPN.SB in Hdisj. lia. }
  destruct (RPPSPEC M beg n usp R (Z_to_bv 64 ret) b1 ltac:(lia) ltac:(lia) Hbeg8 BAND
              ltac:(lia) Hdisj2 Hz Hlast Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.

Lemma and_m8_is_8srl : forall x : word,
  alu64 ALU_AND x (Z_to_bv 64 (2 ^ 64 - 8)) = mul_div M_MUL (Z_to_bv 64 8) (alu64 ALU_SRL x (Z_to_bv 64 3)).
Proof.
  intros x. pose proof (u64_range x) as Hx. apply bv_eq.
  rewrite u_and64, u_mul64, (srl3_div8 x (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity).
  rewrite (u64_lit (2 ^ 64 - 8)) by lia. rewrite land_m8 by lia. rewrite (u64_lit 8) by lia.
  assert (0 <= bv_unsigned x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (zbv_u (bv_unsigned x / 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma respell8_denot : forall E M k e,
  know_ok SEGS E M k -> edenot E (PGN.respell8 k e) = edenot E e.
Proof.
  intros E M k e HK. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo w a IHa|sx kk i w]; cbn [PGN.respell8]; try reflexivity.
  - destruct op; cbn [edenot]; rewrite ?IHa, ?IHb; try reflexivity.
    destruct b as [c| | | | | | |]; cbn [edenot]; rewrite ?IHa, ?IHb; try reflexivity.
    destruct (Z.eqb_spec (c mod two64) (two64 - 8)) as [Ec|]; cbn [edenot]; rewrite ?IHa; [|reflexivity].
    rewrite (mkSrl_denot SEGS E M k (PGN.respell8 k a) 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)). rewrite IHa.
    replace (Z_to_bv 64 c) with (Z_to_bv 64 (2 ^ 64 - 8)); [symmetry; apply and_m8_is_8srl|].
    apply bv_eq. rewrite !u_lit64. unfold two64 in *. rewrite Ec. reflexivity.
  - cbn [edenot]. rewrite IHa, IHb. reflexivity.
Qed.

Theorem node_and2srl_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_and2srl cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk.
  unfold PGN.node_and2srl in Hn. destruct args as [|[r| | | | | | |] [|]]; try discriminate.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. cbn [negb] in Hn.
  apply andb_prop in Hc as [Hr1 Hr32]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr32.
  pose proof HC as HKN. apply co_know in HKN.
  injection Hn as <-.
  assert (Hden : edenot E (PGN.respell8 (kn cs) (reg cs (Z.to_nat r))) = edenot E (reg cs (Z.to_nat r))).
  { apply (respell8_denot E (Mr A argH E cs model FULL)). exact HKN. }
  assert (HC' : cs_ok SEGS A LIMIT SINV argH FS0 E (set_reg cs (Z.to_nat r) (PGN.respell8 (kn cs) (reg cs (Z.to_nat r)))) R FULL model).
  { destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; [|reflexivity].
    apply regs_ok_respell; [assumption | lia | exact Hden]. }
  assert (Hpc' : pc (set_reg cs (Z.to_nat r) (PGN.respell8 (kn cs) (reg cs (Z.to_nat r)))) = pc cs) by reflexivity.
  rewrite <- Hpc'. apply (Hk E R FULL model); [split; apply env_agree_refl | exact HC' | reflexivity].
Qed.

(* [comment removed for export] *)
Theorem node_rpinS_sound : forall eB eN,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_rpinS SEGS nx0 T cs eB eN).
Proof.
  intros eB eN cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold PGN.node_rpinS in Hn.
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  unfold PGN.rpin_testsS in Hn. change PGN.SB with RPN.SB in Hn.
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (split_lit (eadd (mkSrl (kn cs) eB 3) (ELit RPN.SB))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) eB) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) eB) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  destruct (xlo (kn cs) eN) as [Nlo|] eqn:HNlo; [|discriminate].
  destruct (xhi (kn cs) eN) as [Nhi|] eqn:HNhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Htests; [|discriminate] end.
  cbn [forallb] in Htests.
  apply andb_prop in Htests as [Hn16 Htests]. apply andb_prop in Htests as [Hn40 Htests]. apply andb_prop in Htests as [Hal Htests].
  apply andb_prop in Htests as [HalN Htests]. apply andb_prop in Htests as [HN0 Htests].
  apply andb_prop in Htests as [Hblo' Htests]. apply andb_prop in Htests as [Hbhi' Htests].
  apply andb_prop in Htests as [Hsplo' Htests]. apply andb_prop in Htests as [Hsphi' Htests]. apply andb_prop in Htests as [Hdisj Htests].
  apply andb_prop in Htests as [P1 Htests]. apply andb_prop in Htests as [P2 Htests]. apply andb_prop in Htests as [P3 Htests].
  apply andb_prop in Htests as [P4 Htests]. apply andb_prop in Htests as [P5 Htests]. apply andb_prop in Htests as [P6 Htests].
  apply andb_prop in Htests as [P7 Htests]. apply andb_prop in Htests as [P8 Htests].
  apply andb_prop in Htests as [B1 Htests]. apply andb_prop in Htests as [B2 Htests]. apply andb_prop in Htests as [B3 Htests].
  apply andb_prop in Htests as [B4 Htests]. apply andb_prop in Htests as [B5 Htests]. apply andb_prop in Htests as [B6 Htests].
  apply andb_prop in Htests as [B7 Htests]. apply andb_prop in Htests as [B8 Htests].
  apply andb_prop in Htests as [Hwr Htests]. apply andb_prop in Htests as [Hflq Htests].
  apply andb_prop in Htests as [Hge1 Htests]. apply andb_prop in Htests as [Hge2 Htests].
  apply andb_prop in Htests as [Hflh Htests]. apply andb_prop in Htests as [Hkz Htests].
  apply andb_prop in Htests as [Igsb Htests]. apply andb_prop in Htests as [Igm1 Htests]. apply andb_prop in Htests as [Igm2 Htests].
  apply andb_prop in Htests as [Ighi Htests]. apply andb_prop in Htests as [Icm1 Htests]. apply andb_prop in Htests as [Icm2 Htests].
  apply andb_prop in Htests as [Lsb Htests]. apply andb_prop in Htests as [Lhi _].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hal. apply Z.leb_le in HalN. apply Z.leb_le in HN0.
  apply Z.ltb_lt in Hbhi'.
  apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj. unfold two64 in Hsphi'.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (Bw := edenot E eB) in *.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN HNlo) as HNlo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN HNhi) as HNhi2.
  set (Nw := edenot E eN) in *. set (N := bv_unsigned Nw) in *.
  pose proof (u64_range Nw) as HNr. fold N in HNr.
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) eN HKN) as [_ HeaN]. fold Nw in HeaN.
  assert (HN8 : N mod 8 = 0).
  { unfold N. destruct HeaN as [qq Hqq]. rewrite Hqq. replace (ealign (kn cs) eN) with ((ealign (kn cs) eN - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *. set (B := bv_unsigned Bw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr. pose proof (u64_range Bw) as HBr. fold B in HBr.
  (* [comment removed for export] *)
  assert (BAND : B + N <= RPN.kLowEnd \/ (RPN.kHighBeg <= B /\ B + N <= RPN.kHighEnd)).
  { rewrite off_bandL_or in Hblo'. apply orb_prop in Hblo' as [Hx|Hx].
    - apply andb_prop in Hx as [Hx1 Hx2]. apply Z.leb_le in Hx1. apply Z.leb_le in Hx2. right. lia.
    - pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model eB 0 eN HC Hx) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off edenot] in OB. rewrite Z.add_0_r in OB. fold Bw in OB. fold B in OB.
      fold Nw N in OB.
      specialize (OB ltac:(lia)). unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd, LOWTOP, KHI, TOPMAX, STK in *. lia. }
  assert (Hbhi'' : B + N <= 0x7fffffffffff) by (unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in BAND; lia).
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hge1) as G1. cbn [xt_den] in G1. fold begw Bw beg B in G1.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hge2) as G2. cbn [xt_den] in G2. fold begw Bw nw Nw beg B n N in G2.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) eB HKN) as [_ Hea]. fold Bw in Hea.
  assert (HB8 : B mod 8 = 0).
  { unfold B. destruct Hea as [qq Hqq]. rewrite Hqq. replace (ealign (kn cs) eB) with ((ealign (kn cs) eB - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (mkSrl (kn cs) eN 3) HKN HKN Hkz) as (Zb & Z0 & Z1).
  unfold elenZ in Zb, Z1. rewrite (u_srl3 SEGS E M (kn cs) eN HKN) in Zb, Z1. fold Nw N in Zb, Z1.
  assert (HN8r : 0 <= N / 8 < 2 ^ 64) by (unfold RPN.kHighEnd in *; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hq2 : 2 <= N / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HH0 : estart E (SA hb hk) = RPN.SB + B / 8).
  { apply (sh_split_estart E M (kn cs) eB hb hk (N / 8) HKN Hsh Z0 Z1). lia. }
  assert (Hz : forall i, 0 <= i < N / 8 -> M (Z_to_bv 64 (RPN.SB + B / 8 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite <- HH0. apply Zb. exact Hi. }
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hdisj2 : RPN.SB + (B + N - 1) / 8 < usp - 72).
  { assert ((B + N - 1) / 8 <= (bhi + Nhi - 1) / 8) by (apply Z.div_le_mono; lia). unfold RPN.SB. unfold PGN.SB, RPN.SB in Hdisj. lia. }
  destruct (RPINSPEC M beg n usp B N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) HB8 HN8 ltac:(lia) ltac:(lia)
              BAND ltac:(lia) Hdisj2 Hz Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.


(* [comment removed for export] *)
Theorem node_rpin_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => PGN.node_rpin SEGS nx0 T cs args).
Proof.
  intros args cs cs' E R FULL model TT HC HX Hn Hk.
  unfold PGN.node_rpin in Hn. destruct args as [|eB [|eN [|x rest]]]; try discriminate.
  2: { destruct eN; discriminate. }
  destruct eN as [N| | | | | | |]; [| exact (node_rpinS_sound eB _ cs cs' E R FULL model TT HC HX Hn Hk) ..].   (* [comment removed for export] *)
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  unfold PGN.rpin_tests in Hn. change PGN.SB with RPN.SB in Hn.
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (split_lit (eadd (mkSrl (kn cs) eB 3) (ELit RPN.SB))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) eB) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) eB) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Htests; [|discriminate] end.
  cbn [forallb] in Htests.
  apply andb_prop in Htests as [Hn16 Htests]. apply andb_prop in Htests as [Hn40 Htests]. apply andb_prop in Htests as [Hal Htests].
  apply andb_prop in Htests as [HN8 Htests]. apply andb_prop in Htests as [HN0 Htests].
  apply andb_prop in Htests as [Hblo' Htests]. apply andb_prop in Htests as [Hbhi' Htests].
  apply andb_prop in Htests as [Hsplo' Htests]. apply andb_prop in Htests as [Hsphi' Htests]. apply andb_prop in Htests as [Hdisj Htests].
  apply andb_prop in Htests as [P1 Htests]. apply andb_prop in Htests as [P2 Htests]. apply andb_prop in Htests as [P3 Htests].
  apply andb_prop in Htests as [P4 Htests]. apply andb_prop in Htests as [P5 Htests]. apply andb_prop in Htests as [P6 Htests].
  apply andb_prop in Htests as [P7 Htests]. apply andb_prop in Htests as [P8 Htests].
  apply andb_prop in Htests as [B1 Htests]. apply andb_prop in Htests as [B2 Htests]. apply andb_prop in Htests as [B3 Htests].
  apply andb_prop in Htests as [B4 Htests]. apply andb_prop in Htests as [B5 Htests]. apply andb_prop in Htests as [B6 Htests].
  apply andb_prop in Htests as [B7 Htests]. apply andb_prop in Htests as [B8 Htests].
  apply andb_prop in Htests as [Hwr Htests]. apply andb_prop in Htests as [Hflq Htests].
  apply andb_prop in Htests as [HflB Htests]. apply andb_prop in Htests as [Hge1 Htests]. apply andb_prop in Htests as [Hge2 Htests].
  apply andb_prop in Htests as [Hflh Htests]. apply andb_prop in Htests as [Hkz Htests].
  apply andb_prop in Htests as [Igsb Htests]. apply andb_prop in Htests as [Igm1 Htests]. apply andb_prop in Htests as [Igm2 Htests].
  apply andb_prop in Htests as [Ighi Htests]. apply andb_prop in Htests as [Icm1 Htests]. apply andb_prop in Htests as [Icm2 Htests].
  apply andb_prop in Htests as [Lsb Htests]. apply andb_prop in Htests as [Lhi _].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hal. apply Z.eqb_eq in HN8. apply Z.ltb_lt in HN0.
  apply Z.ltb_lt in Hbhi'.
  apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj. unfold two64 in Hsphi'.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (Bw := edenot E eB) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *. set (B := bv_unsigned Bw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr. pose proof (u64_range Bw) as HBr. fold B in HBr.
  (* [comment removed for export] *)
  assert (BAND : B + N <= RPN.kLowEnd \/ (RPN.kHighBeg <= B /\ B + N <= RPN.kHighEnd)).
  { rewrite off_bandL_or in Hblo'. apply orb_prop in Hblo' as [Hx|Hx].
    - apply andb_prop in Hx as [Hx1 Hx2]. apply Z.leb_le in Hx1. apply Z.leb_le in Hx2. right. lia.
    - pose proof (off_band_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model eB 0 (ELit N) HC Hx) as OB.
      unfold estart, elenZ in OB. cbn [a_base a_off edenot] in OB. rewrite Z.add_0_r in OB. fold Bw in OB. fold B in OB.
      rewrite u64_lit in OB by (unfold RPN.kHighEnd in *; lia).
      specialize (OB ltac:(lia)). unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd, LOWTOP, KHI, TOPMAX, STK in *. lia. }
  assert (Hbhi'' : B + N <= 0x7fffffffffff) by (unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in BAND; lia).
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hge1) as G1. cbn [xt_den] in G1. fold begw Bw beg B in G1.
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hge2) as G2. cbn [xt_den] in G2. fold begw Bw nw beg B n in G2.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M (kn cs) eB HKN) as [_ Hea]. fold Bw in Hea.
  assert (HB8 : B mod 8 = 0).
  { unfold B. destruct Hea as [qq Hqq]. rewrite Hqq. replace (ealign (kn cs) eB) with ((ealign (kn cs) eB - 3) + 3) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. rewrite Z.mul_assoc. apply Z_mod_mult. }
  (* [comment removed for export] *)
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit (N / 8)) HKN HKN Hkz) as (Zb & Z0 & Z1).
  unfold elenZ in Zb, Z1. cbn [edenot] in Zb, Z1.
  assert (HN8r : 0 <= N / 8 < 2 ^ 64) by (unfold RPN.kHighEnd in *; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite u64_lit in Zb, Z1 by lia.
  assert (Hq2 : 2 <= N / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HH0 : estart E (SA hb hk) = RPN.SB + B / 8).
  { apply (sh_split_estart E M (kn cs) eB hb hk (N / 8) HKN Hsh Z0 Z1). lia. }
  assert (Hz : forall i, 0 <= i < N / 8 -> M (Z_to_bv 64 (RPN.SB + B / 8 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite <- HH0. apply Zb. exact Hi. }
  (* [comment removed for export] *)
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound SEGS E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound SEGS E M (kn cs) _ _ HKN B8 Lhi) as C8.
  (* [comment removed for export] *)
  assert (Hdisj2 : RPN.SB + (B + N - 1) / 8 < usp - 72).
  { assert ((B + N - 1) / 8 <= (bhi + N - 1) / 8) by (apply Z.div_le_mono; lia). unfold RPN.SB. unfold PGN.SB, RPN.SB in Hdisj. lia. }
  destruct (RPINSPEC M beg n usp B N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) HB8 HN8 ltac:(lia) ltac:(lia)
              BAND ltac:(lia) Hdisj2 Hz Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.

Theorem pg_xn_sound : ext_stmt SEGS A nx0 LIMIT (PGN.xn SEGS nx0 T) SINV argH FS0.
Proof.
  intros id args. unfold PGN.xn.
  destruct (Nat.eqb id 105); [apply node_pgran_sound|].
  destruct (Nat.eqb id 106); [apply node_isrc_sound|].
  destruct (Nat.eqb id 107); [apply node_idst_sound|].
  destruct (Nat.eqb id 108); [apply node_rppart_sound|].
  destruct (Nat.eqb id 109); [apply node_and2srl_sound|].
  destruct (Nat.eqb id 110); [apply node_rpin_sound|].
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
