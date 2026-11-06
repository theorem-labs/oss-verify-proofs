(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells AQuar ATacFix.
Import ListNotations.
Open Scope Z_scope.

Definition merge_entry : Z := 0x355f4.

Fixpoint copy_into (dst : list word) (off : nat) (src : list word) : list word :=
  match src with [] => dst | w :: r => copy_into (upd dst off w) (S off) r end.

Lemma copy_into_length : forall src dst off, length (copy_into dst off src) = length dst.
Proof. induction src as [|w r IH]; intros dst off; cbn [copy_into]; [reflexivity|]. rewrite IH. apply upd_length. Qed.

Lemma firstn_upd_ge : forall {X} (l : list X) i x n, (n <= i)%nat -> firstn n (upd l i x) = firstn n l.
Proof.
  induction l as [|y l IH]; intros i x n Hn; [destruct i; reflexivity|].
  destruct i as [|i]; [replace n with 0%nat by lia; reflexivity|]. destruct n as [|n]; [reflexivity|]. cbn [upd firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_copy_into_lt : forall src dst off n, (n <= off)%nat -> firstn n (copy_into dst off src) = firstn n dst.
Proof.
  induction src as [|w r IH]; intros dst off n Hn; cbn [copy_into]; [reflexivity|]. rewrite IH by lia. apply firstn_upd_ge. exact Hn.
Qed.

Lemma firstn_S_upd : forall {X} (l : list X) i x, (i < length l)%nat -> firstn (S i) (upd l i x) = firstn i l ++ [x].
Proof.
  induction l as [|y l IH]; intros i x Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|]. cbn [upd firstn app]. rewrite IH by (cbn in Hi; lia). reflexivity.
Qed.

Lemma firstn_copy_into : forall src dst off, (off + length src <= length dst)%nat ->
  firstn (off + length src) (copy_into dst off src) = firstn off dst ++ src.
Proof.
  induction src as [|w r IH]; intros dst off Hl; cbn [copy_into length].
  - rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - cbn [length] in Hl. replace (off + S (length r))%nat with (S off + length r)%nat by lia. rewrite IH by (rewrite upd_length; lia).
    rewrite firstn_S_upd by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma skipn_firstn_cons {X} : forall (l : list X) i n x,
  nth_error l i = Some x -> (i < n)%nat -> skipn i (firstn n l) = x :: skipn (S i) (firstn n l).
Proof.
  intros l i n x Hn Hi. revert l n Hn Hi. induction i as [|i IH]; intros [|y l] [|n] Hn Hi; cbn in *; try discriminate; try lia.
  - inversion Hn; reflexivity.
  - apply IH; [exact Hn| lia].
Qed.

Lemma copy_loop : forall (k i : nat) (ra sp gp tp x5 x6 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (NA CA : Z) (nws cws : list word) (cc nc len : nat),
  mem_inv asegs m -> u64arr asegs m NA nws -> u64arr asegs m CA cws -> length cws = len ->
  (i + S k = nc)%nat -> (nc <= length nws)%nat -> (cc + nc <= len)%nat ->
  (NA + 8 * Z.of_nat (length nws) <= CA \/ CA + 8 * Z.of_nat len <= NA) ->
  evt asegs (fun ms' => exists x30' m',
      ms' = MS (mkR ra sp gp tp x5 x6 (wz (NA + 8 * Z.of_nat nc)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   (wz (CA + 8 * Z.of_nat (cc + nc))) (wz (NA + 8 * Z.of_nat nc)) x30' x31)
               F (wz 0x35678) fc None m' (seg_rom asegs)
      /\ munch [(CA, CA + 8 * Z.of_nat len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ u64arr asegs m' NA nws /\ u64arr asegs m' CA (copy_into cws (cc + i) (skipn i (firstn nc nws))))
    (MS (mkR ra sp gp tp x5 x6 (wz (NA + 8 * Z.of_nat i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (wz (CA + 8 * Z.of_nat (cc + i))) (wz (NA + 8 * Z.of_nat nc)) x30 x31)
        F (wz 0x35664) fc None m (seg_rom asegs)).
Proof.
  intros k; induction k as [|k IH]; intros until len; intros MI NWS CWS LEN IK NLE CLE SEP.
  all: pose proof (u64arr_bound asegs m NA nws NWS) as NB; pose proof (u64arr_bound asegs m CA cws CWS) as CB.
  all: pose proof (munch_refl [(CA, CA + 8 * Z.of_nat len)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: destruct (nth_error nws i) as [w|] eqn:NTH; [| exfalso; apply nth_error_None in NTH; lia].
  all: remember (NA + 8 * Z.of_nat i) as SRC eqn:HSRC; remember (CA + 8 * Z.of_nat (cc + i)) as DST eqn:HDST.
  all: pose proof (u64arr_read asegs m NA nws (Z.of_nat i) w (wa SRC) NWS ltac:(rewrite Nat2Z.id; exact NTH) ltac:(lia) ltac:(rewrite HSRC; reflexivity)) as HR.
  all: pose proof (u64arr_store_ok asegs m CA cws (Z.of_nat (cc + i)) (wa DST) CWS ltac:(lia) ltac:(rewrite HDST; reflexivity)) as SOK.
  all: zstep.
  all: zstep.
  all: zstep.

  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
         pose proof (u64arr_write asegs mx CA cws (Z.of_nat (cc + i)) w CWS ltac:(lia)) as CWS2 end.
  all: rewrite <- HDST in CWS2; rewrite Nat2Z.id in CWS2.
  all: clear CWS; store_done; rename CWS2 into CWS.
  all: zstep.
  all: rewrite (skipn_firstn_cons nws i nc w NTH) by lia; cbn [copy_into].

  -
    zstep. if_cases KB; zify_cond KB. { exfalso. clear - KB HSRC IK NB NLE. lia. } clear KB.
    replace (SRC + 8) with (NA + 8 * Z.of_nat nc) by lia. replace (DST + 8) with (CA + 8 * Z.of_nat (cc + nc)) by lia.
    rewrite skipn_all2 by (rewrite length_firstn; lia). cbn [copy_into].
    finish.
  -
    zstep. if_cases KB; zify_cond KB; [| exfalso; clear - KB HSRC IK NB NLE; lia]. clear KB.
    replace (SRC + 8) with (NA + 8 * Z.of_nat (S i)) by lia. replace (DST + 8) with (CA + 8 * Z.of_nat (cc + S i)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (IH (S i) ra sp gp tp x5 x6 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w x31 F fc mm NA CA nws (upd cws (cc + i) w) cc nc len
              MIx NWS CWS ltac:(rewrite upd_length; exact LEN) ltac:(lia) NLE CLE SEP) end end.
    replace (cc + S i)%nat with (S (cc + i)) by lia.
    finish.
    replace (cc + S i)%nat with (S (cc + i)) in * by lia. assumption.
Qed.

Section MSTEP.
  Variables (G T : Z).

  Definition mstep_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (CA NA : Z) (nnx : word) (cs ns cc nc : Z) (cws nws : list word) (gc : Z) (gf : word) (GL : Z) (gb : word)
      (tc : Z) (tf tl : word) (tb : Z) (EA : Z) (es ec : word) (ex8 : Z) : machine_state -> Prop :=
    fun ms' => exists x6 x7 a3 x28 x29 x30 m',
      ms' = MS (mkR ra sp gp tp (wz NA) x6 x7 s0 s1 (wz G) (wz T) (wz (ex8 + 8192)) a3 (wz CA) (wz 1021) (wz (-8192)) (wz 8192)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35708) fc None m' (seg_rom asegs)
      /\ munch [(G, G + 32); (T, T + 32); (CA, CA + 8192); (NA, NA + 8192); (EA, EA + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' CA [C8 nnx; C8 (wz (cs + ns - 8192)); C8 (wz (cc + nc))]
      /\ u64arr asegs m' (CA + 24) (copy_into cws (Z.to_nat cc) (firstn (Z.to_nat nc) nws))
      /\ rw_cells asegs m' NA [C8 (wz 0); C8 (wz 8192); C8 (wz 0)]
      /\ u64arr asegs m' (NA + 24) nws
      /\ rw_cells asegs m' G [C8 (wz (gc - 1)); C8 gf; C8 (wz (if GL =? NA then CA else GL)); C8 gb]
      /\ rw_cells asegs m' T [C8 (wz (tc + 1)); C8 (if tc =? 0 then wz NA else tf); C8 (wz NA); C8 (wz (tb + 8192))]
      /\ (tc <> 0 -> rw_cells asegs m' EA [C8 (wz NA); C8 es; C8 ec]).

  #[using="Type"] Lemma merge_step : forall (ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (CA NA : Z) (cnx nnx : word) (cs ns cc nc : Z) (cws nws : list word) (gc : Z) (gf : word) (GL : Z) (gb : word)
      (tc : Z) (tf tl : word) (tb : Z) (EA : Z) (enx es ec : word) (ex8 : Z),
    mem_inv asegs m ->
    rw_cells asegs m CA [C8 cnx; C8 (wz cs); C8 (wz cc)] -> u64arr asegs m (CA + 24) cws -> length cws = 1021%nat ->
    rw_cells asegs m NA [C8 nnx; C8 (wz ns); C8 (wz nc)] -> u64arr asegs m (NA + 24) nws -> length nws = 1021%nat ->
    rw_cells asegs m G [C8 (wz gc); C8 gf; C8 (wz GL); C8 gb] ->
    rw_cells asegs m T [C8 (wz tc); C8 tf; C8 tl; C8 (wz tb)] ->
    (tc <> 0 -> tl = wz EA /\ rw_cells asegs m EA [C8 enx; C8 es; C8 ec]) ->
    8192 <= cs < 2^63 -> 0 <= ns < 2^63 -> 0 <= cc -> 1 <= nc -> cc + nc <= 1021 -> 1 <= gc < 2^64 -> 0 <= tc < 2^63 -> 0 <= GL < 2^64 ->
    0 < CA -> 0 < NA -> NA + 8192 < 2^64 -> CA + 8192 < 2^64 ->
    (CA + 8192 <= NA \/ NA + 8192 <= CA) ->
    0 <= G -> G + 32 <= CA -> G + 32 <= NA -> CA + 8192 <= T -> NA + 8192 <= T -> T + 32 < 2^64 ->
    (tc <> 0 -> G + 32 <= EA /\ EA + 24 <= T /\ (EA + 24 <= CA \/ CA + 8192 <= EA) /\ (EA + 24 <= NA \/ NA + 8192 <= EA)) ->
    evt asegs (mstep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 F fc m CA NA nnx cs ns cc nc cws nws gc gf GL gb tc tf tl tb EA es ec ex8)
      (MS (mkR ra sp gp tp (wz NA) (wz (nc + cc)) x7 s0 s1 (wz G) (wz T) (wz ex8) a3 (wz CA) (wz 1021) (wz (-8192)) (wz 8192)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz nc) (wz cc) x30 x31)
          F (wz 0x3563c) fc None m (seg_rom asegs)).
  Proof.
    intros ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 F fc m CA NA cnx nnx cs ns cc nc cws nws gc gf GL gb tc tf tl tb EA enx es ec ex8
      MI CH CW LCW NH NW LNW GC TC EL CS NS CC0 NC1 CNL GC1 TC0 GLR CA0 NA0 NAH CAH SEP G0 GCA GNA CAT NAT TH EG.
    pose proof (munch_refl [(G, G + 32); (T, T + 32); (CA, CA + 8192); (NA, NA + 8192); (EA, EA + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.

    assert (EH : tc = 0 \/ (tc <> 0 /\ tl = wz EA /\ rw_cells asegs m EA [C8 enx; C8 es; C8 ec])) by (destruct (Z.eq_dec tc 0) as [E0|N0]; [left; exact E0| right; split; [exact N0| exact (EL N0)]]).
    clear EL. destruct EH as [TC0'|(TCN & ETL & EH)]; [subst tc; clear EG| subst tl; destruct (EG TCN) as (GEA & EAT & SEPC & SEPN); clear EG].
    all: zstep.
    all: zstep.
    all: zstep; if_cases KB; zify_cond KB.

    all: try (exfalso; rewrite Z.shiftr_div_pow2 in KB by lia; clear - KB CS; change (2 ^ 13) with 8192 in KB; Z.div_mod_to_equations; lia).
    all: clear KB.
    all: zstep; if_cases KB; zify_cond KB; [exfalso; clear - KB NC1; lia|]; clear KB.
    all: do 6 zstep.
    all: replace (Z_to_bv 64 (NA + 24 + Z.shiftl nc 3)) with (wz (NA + 24 + 8 * Z.of_nat (Z.to_nat nc))) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: replace (Z_to_bv 64 (CA + Z.shiftl cc 3 + 24)) with (wz (CA + 24 + 8 * Z.of_nat (Z.to_nat cc + 0))) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: replace (Z_to_bv 64 (NA + 24)) with (wz (NA + 24 + 8 * Z.of_nat 0)) by (f_equal; lia).
    all: call (copy_loop (Z.to_nat nc - 1) 0 ra sp gp tp (wz NA) (wz (nc + cc)) s0 s1 (wz G) (wz T) (wz ex8) (wz cs) (wz CA) (wz 1021) (wz (-8192)) (wz 8192)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (Z.shiftl nc 3)) x31 F fc m (NA + 24) (CA + 24) nws cws (Z.to_nat cc) (Z.to_nat nc) 1021%nat
                 MI NW CW LCW ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    all: rewrite Nat.add_0_r, skipn_O in POST.
    all: pose proof (copy_into_length (firstn (Z.to_nat nc) nws) cws (Z.to_nat cc)) as LCP; rewrite LCW in LCP.

    all: do 4 zstep.
    all: do 2 zstep.
    all: do 2 sstep.
    all: zstep; if_cases KB; zify_cond KB; [exfalso; clear - KB GC1; lia|]; clear KB.
    all: do 3 zstep.
    all: zstep; if_cases KL; zify_cond KL.

    -
      zstep.
      do 3 zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT. lia. } clear KT.
      zstep.
      zstep.
      sstep.
      zstep.
      do 4 zstep.

      replace (nc + cc) with (cc + nc) in CH by lia.
      unfold mstep_post. rewrite (proj2 (Z.eqb_eq GL NA) KL). cbn [Z.eqb].
      finish.
      intros C0. exfalso. apply C0. reflexivity.

    -
      do 3 zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT; [| exfalso; clear - KT; lia]. clear KT.
      zstep.
      zstep.
      sstep.
      zstep.
      do 4 zstep.
      replace (nc + cc) with (cc + nc) in CH by lia.
      unfold mstep_post. rewrite (proj2 (Z.eqb_neq GL NA) KL). cbn [Z.eqb].
      finish.
      intros C0. exfalso. apply C0. reflexivity.

    -
      zstep.
      do 3 zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT; [| exfalso; clear - KT TCN TC0; lia]. clear KT.
      zstep.
      zstep.
      do 2 zstep.
      zstep.
      zstep.
      do 4 zstep.
      replace (nc + cc) with (cc + nc) in CH by lia.
      unfold mstep_post. rewrite (proj2 (Z.eqb_eq GL NA) KL). rewrite (proj2 (Z.eqb_neq tc 0) TCN).
      finish.
      intros _. exact EH.

    -
      do 3 zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT TCN TC0. lia. } clear KT.
      zstep.
      zstep.
      do 2 zstep.
      zstep.
      zstep.
      do 4 zstep.
      replace (nc + cc) with (cc + nc) in CH by lia.
      unfold mstep_post. rewrite (proj2 (Z.eqb_neq GL NA) KL). rewrite (proj2 (Z.eqb_neq tc 0) TCN).
      finish.
      intros _. exact EH.
  Qed.
End MSTEP.

Lemma outside_In : forall W x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof.
  induction W as [|[lo hi] W IH]; intros x iv O Hin; [destruct Hin|]. cbn [outside] in O. destruct O as [O1 O2].
  destruct Hin as [<-|Hin]; [exact O1| exact (IH x iv O2 Hin)].
Qed.
Lemma outside_of_In : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x HA; cbn [outside]; [exact I|]. split; [exact (HA (lo, hi) (or_introl eq_refl))|].
  apply IH. intros iv Hin. apply HA. right. exact Hin.
Qed.
Lemma sub_fp_incl : forall W1 W2, incl W1 W2 -> sub_fp W1 W2.
Proof. intros W1 W2 I12 x O. apply outside_of_In. intros iv Hin. exact (outside_In W2 x iv O (I12 iv Hin)). Qed.

Section MERGE.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Variables (G T : Z).
  Hypothesis G0 : 0 <= G.
  Hypothesis TH : T + 32 < 2^64.

  Definition qb_main (m : mem) (b : qbatch) (nx : Z) : Prop :=
    rw_cells asegs m (qb_addr AL b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
    /\ exists ws, u64arr asegs m (qb_addr AL b + 24) ws /\ length ws = 1021%nat
                  /\ firstn (length (qb_chunks b)) ws = map (fun ch => wz (qc_hdr AL ch)) (qb_chunks b).
  Fixpoint qmain_list (m : mem) (l : list qbatch) (nxt : Z) {struct l} : Prop :=
    match l with
    | [] => True
    | b :: l' => qb_main m b (match l' with [] => nxt | b' :: _ => qb_addr AL b' end) /\ qmain_list m l' nxt
    end.

  #[using="Type"] Lemma qmain_list_snoc : forall m l b nxt, qmain_list m (l ++ [b]) nxt <-> qmain_list m l (qb_addr AL b) /\ qb_main m b nxt.
  Proof.
    intros m l b nxt. induction l as [|a l IH]; cbn [qmain_list app].
    - tauto.
    - rewrite IH. destruct l as [|a' l']; cbn [app]; tauto.
  Qed.

  #[using="Type"] Lemma qb_main_frame : forall W m m' b nx, qb_main m b nx -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (qb_addr AL b) 8192 -> qb_main m' b nx.
  Proof.
    intros W m m' b nx (HC3 & (ws & AR & LW & FW)) MU WM D1. split.
    - eapply rw_cells_transport; [exact HC3| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| cbn; lia| cbn; lia].
    - exists ws. split; [| split; assumption]. eapply u64arr_transport; [exact AR| exact MU| exact WM|].
      eapply disjoint_from_sub; [exact D1| lia| rewrite LW; lia].
  Qed.
  #[using="Type"] Lemma qmain_list_frame : forall W m m' l nxt, qmain_list m l nxt -> munch W m m' -> wmono asegs m m' ->
    Forall (fun b => disjoint_from W (qb_addr AL b) 8192) l -> qmain_list m' l nxt.
  Proof.
    intros W m m' l nxt R MU WM Fd. revert R. induction Fd as [|b l D1 Fd IH]; cbn [qmain_list]; [tauto|].
    intros [RB RL]. split; [eapply qb_main_frame; eassumption| exact (IH RL)].
  Qed.

  Definition biv (b : qbatch) : Z * Z := (qb_addr AL b, qb_addr AL b + 8192).
  Definition bgeo (b : qbatch) : Prop := G + 64 <= qb_addr AL b /\ qb_addr AL b + 8192 <= T /\ (16 * qb_v b) mod 8192 = 0.
  #[using="Type"] Lemma bapart_of : forall b1 b2, bgeo b1 -> bgeo b2 -> qb_v b1 <> qb_v b2 ->
    qb_addr AL b1 + 8192 <= qb_addr AL b2 \/ qb_addr AL b2 + 8192 <= qb_addr AL b1.
  Proof. intros b1 b2 (_ & _ & M1) (_ & _ & M2) NE. unfold qb_addr. Z.div_mod_to_equations. lia. Qed.

  #[using="Type"] Lemma dj_batches : forall L b, bgeo b -> Forall bgeo L -> ~ In (qb_v b) (map qb_v L) ->
    disjoint_from ((G, G + 32) :: (T, T + 32) :: map biv L) (qb_addr AL b) 8192.
  Proof.
    intros L b GB FL NI. pose proof GB as (B1 & B2 & _). cbn [disjoint_from]. split; [lia|]. split; [lia|].
    induction FL as [|b' L GB' FL IH]; cbn [map disjoint_from]; [exact I|].
    cbn [map] in NI. split; [| apply IH; intros C; apply NI; right; exact C].
    destruct (bapart_of b b' GB GB' ltac:(intros C; apply NI; left; symmetry; exact C)) as [A|A]; unfold biv; cbn [fst snd]; lia.
  Qed.

  Definition merged (cur nx : qbatch) : qbatch := mkQB (qb_v cur) (qb_size cur + qb_size nx - Q_BBYTES) (qb_chunks cur ++ qb_chunks nx).
  Definition emptied (nx : qbatch) : qbatch := mkQB (qb_v nx) Q_BBYTES [].

  #[using="Type"] Lemma q_merge_keep : forall cur nx rest, Q_BATCH < qb_count cur + qb_count nx ->
    q_merge cur (nx :: rest) = (cur :: fst (q_merge nx rest), snd (q_merge nx rest)).
  Proof.
    intros cur nx rest K. cbn [q_merge]. replace (qb_count cur + qb_count nx <=? Q_BATCH) with false by (symmetry; apply Z.leb_gt; exact K).
    destruct (q_merge nx rest) as [l e]. reflexivity.
  Qed.
  #[using="Type"] Lemma q_merge_take : forall cur nx rest, qb_count cur + qb_count nx <= Q_BATCH ->
    q_merge cur (nx :: rest) = (fst (q_merge (merged cur nx) rest), emptied nx :: snd (q_merge (merged cur nx) rest)).
  Proof.
    intros cur nx rest K. cbn [q_merge]. replace (qb_count cur + qb_count nx <=? Q_BATCH) with true by (symmetry; apply Z.leb_le; exact K).
    fold (merged cur nx). fold (emptied nx). destruct (q_merge (merged cur nx) rest) as [l e]. reflexivity.
  Qed.
  #[using="Type"] Lemma q_merge_first : forall rest cur, exists c' l', fst (q_merge cur rest) = c' :: l' /\ qb_v c' = qb_v cur.
  Proof.
    induction rest as [|nx rest IH]; intros cur; [exists cur, []; split; reflexivity|].
    destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
    - rewrite (q_merge_take cur nx rest K). cbn [fst]. destruct (IH (merged cur nx)) as (c' & l' & E1 & E2). exists c', l'. split; [exact E1| exact E2].
    - rewrite (q_merge_keep cur nx rest K). cbn [fst]. exists cur, (fst (q_merge nx rest)). split; reflexivity.
  Qed.

  #[using="Type"] Lemma qlast_cons2 : forall a b l, qlast AL (a :: b :: l) = qlast AL (b :: l).
  Proof.
    intros a b l. destruct (exists_last (l := b :: l) ltac:(discriminate)) as (l' & z & E). rewrite E.
    change (a :: l' ++ [z]) with ((a :: l') ++ [z]). rewrite !qlast_snoc. reflexivity.
  Qed.
  #[using="Type"] Lemma qlast_in : forall b l, exists z, In z (b :: l) /\ qlast AL (b :: l) = qb_addr AL z.
  Proof.
    intros b l. destruct (exists_last (l := b :: l) ltac:(discriminate)) as (l' & z & E). rewrite E. exists z. split; [apply in_or_app; right; left; reflexivity| apply qlast_snoc].
  Qed.
  #[using="Type"] Lemma qb_addr_v : forall b1 b2, qb_v b1 = qb_v b2 -> qb_addr AL b1 = qb_addr AL b2.
  Proof. intros b1 b2 E. unfold qb_addr. rewrite E. reflexivity. Qed.

  Definition bwf (b : qbatch) : Prop := 8192 <= qb_size b /\ 1 <= qb_count b <= 1021.
  Definition bex (b : qbatch) : Prop := qb_size b = 8192 /\ qb_chunks b = [].

  #[using="Type"] Lemma qbytes_cons : forall b l, qbytes (b :: l) = qb_size b + qbytes l. Proof. reflexivity. Qed.
  #[using="Type"] Lemma bwf_qbytes_nonneg : forall l, Forall bwf l -> 0 <= qbytes l.
  Proof. intros l FW. apply qbytes_nonneg. eapply Forall_impl; [| exact FW]. intros b (S8 & _). lia. Qed.

  #[using="Type"] Lemma NoDup_app_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
  Proof.
    induction l1 as [|y l1 IH]; intros l2 x ND H1; [destruct H1|]. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI ND].
    destruct H1 as [->|H1]; [intros H2; apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND H1)].
  Qed.

  Definition miter_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (cur nx : qbatch) (rest ex : list qbatch) (gc : Z) (gf gb : word) : machine_state -> Prop :=
    fun ms' => exists x6 x7 a3 x28 x29 x30 m',
      let ex' := ex ++ [emptied nx] in
      ms' = MS (mkR ra sp gp tp (wz (qb_addr AL nx)) x6 x7 s0 s1 (wz G) (wz T) (wz (8192 * Z.of_nat (length ex'))) a3 (wz (qb_addr AL cur))
                    (wz 1021) (wz (-8192)) (wz 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35708) fc None m' (seg_rom asegs)
      /\ munch ((G, G + 32) :: (T, T + 32) :: map biv (cur :: nx :: rest ++ ex)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ qmain_list m' (merged cur nx :: rest) 0 /\ qmain_list m' ex' 0
      /\ rw_cells asegs m' G [C8 (wz (gc - 1)); C8 gf; C8 (wz (qlast AL (merged cur nx :: rest))); C8 gb]
      /\ rw_cells asegs m' T [C8 (wz (Z.of_nat (length ex'))); C8 (wz (qfirst AL ex')); C8 (wz (qlast AL ex')); C8 (wz (8192 * Z.of_nat (length ex')))].

  #[using="G0 TH"] Lemma merge_iter : forall (rest : list qbatch) (cur nx : qbatch) (ex : list qbatch)
      (ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (gc : Z) (gf gb : word),
    mem_inv asegs m ->
    qmain_list m (cur :: nx :: rest) 0 -> qmain_list m ex 0 ->
    rw_cells asegs m G [C8 (wz gc); C8 gf; C8 (wz (qlast AL (cur :: nx :: rest))); C8 gb] ->
    rw_cells asegs m T [C8 (wz (Z.of_nat (length ex))); C8 (wz (qfirst AL ex)); C8 (wz (qlast AL ex)); C8 (wz (8192 * Z.of_nat (length ex)))] ->
    Z.of_nat (length rest) + 2 <= gc < 2^63 ->
    List.NoDup (map qb_v (cur :: nx :: rest ++ ex)) -> Forall bgeo (cur :: nx :: rest ++ ex) -> Forall bwf (cur :: nx :: rest) -> Forall bex ex ->
    qbytes (cur :: nx :: rest) < 2^62 -> Z.of_nat (length ex) + Z.of_nat (length rest) + 2 < 2^62 ->
    qb_count cur + qb_count nx <= 1021 ->
    evt asegs (miter_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 F fc m cur nx rest ex gc gf gb)
      (MS (mkR ra sp gp tp (wz (qb_addr AL nx)) (wz (qb_count nx + qb_count cur)) x7 s0 s1 (wz G) (wz T) (wz (8192 * Z.of_nat (length ex))) a3
               (wz (qb_addr AL cur)) (wz 1021) (wz (-8192)) (wz 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (qb_count nx)) (wz (qb_count cur)) x30 x31)
          F (wz 0x3563c) fc None m (seg_rom asegs)).
  Proof.
    intros rest cur nx ex ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 F fc m gc gf gb
      MI QL QE GC TC GCR ND FG FW FE QB LE KM.
    pose proof QL as QLc; cbn [qmain_list] in QLc; destruct QLc as ((CH & (cws & CW & LCW & FCW)) & (NH & (nws & NW & LNW & FNW)) & QL2).
    pose proof FG as FG'; apply Forall_cons_iff in FG' as [GCU FG']; apply Forall_cons_iff in FG' as [GNX FGr].
    pose proof FW as FW'; apply Forall_cons_iff in FW' as [(CS8 & CC1 & CC2) FW']; apply Forall_cons_iff in FW' as [(NS8 & NC1 & NC2) FWr].
    pose proof (bwf_qbytes_nonneg _ FWr) as QR0; rewrite !qbytes_cons in QB.
    cbn [map] in ND. pose proof ND as ND'. apply NoDup_cons_iff in ND' as [NI1 ND']. apply NoDup_cons_iff in ND' as [NI2 NDr].
    assert (VNE : qb_v cur <> qb_v nx) by (intros C; apply NI1; left; symmetry; exact C).
    pose proof (bapart_of cur nx GCU GNX VNE) as SEP. pose proof GCU as (GC1 & GC2 & _). pose proof GNX as (GN1 & GN2 & _).

    assert (APO : forall b, In b (rest ++ ex) -> bgeo b /\ (qb_addr AL b + 8192 <= qb_addr AL cur \/ qb_addr AL cur + 8192 <= qb_addr AL b)
                                               /\ (qb_addr AL b + 8192 <= qb_addr AL nx \/ qb_addr AL nx + 8192 <= qb_addr AL b)).
    { intros b Hb. pose proof (proj1 (Forall_forall _ _) FGr b Hb) as GB. split; [exact GB|]. split.
      - apply (bapart_of b cur GB GCU). intros C. apply NI1. right. rewrite <- C. apply in_map. exact Hb.
      - apply (bapart_of b nx GB GNX). intros C. apply NI2. rewrite <- C. apply in_map. exact Hb. }
    set (CA := qb_addr AL cur) in *. set (NA := qb_addr AL nx) in *. set (tc := Z.of_nat (length ex)) in *.
    set (W5 := fun EA : Z => [(G, G + 32); (T, T + 32); (CA, CA + 8192); (NA, NA + 8192); (EA, EA + 24)]).

    assert (EXF : exists (EA : Z) (es ec : word),
              (tc <> 0 -> wz (qlast AL ex) = wz EA /\ rw_cells asegs m EA [C8 (wz 0); C8 es; C8 ec])
              /\ (tc <> 0 -> G + 32 <= EA /\ EA + 24 <= T /\ (EA + 24 <= CA \/ CA + 8192 <= EA) /\ (EA + 24 <= NA \/ NA + 8192 <= EA))
              /\ (exists iv, In iv ((G, G + 32) :: (T, T + 32) :: map biv (cur :: nx :: rest ++ ex)) /\ fst iv <= EA /\ EA + 24 <= snd iv)
              /\ (forall b, In b rest -> qb_addr AL b + 8192 <= EA \/ EA + 24 <= qb_addr AL b)
              /\ (forall m1, munch (W5 EA) m m1 -> wmono asegs m m1 -> (tc <> 0 -> rw_cells asegs m1 EA [C8 (wz NA); C8 es; C8 ec]) ->
                             qb_main m1 (emptied nx) 0 -> qmain_list m1 (ex ++ [emptied nx]) 0)
              /\ (if tc =? 0 then wz NA else wz (qfirst AL ex)) = wz (qfirst AL (ex ++ [emptied nx]))).
    { destruct ex as [|e0 ex0].
      - exists T, (wz 0), (wz 0). subst tc. cbn [length Z.of_nat].
        split; [intros C; exfalso; apply C; reflexivity|]. split; [intros C; exfalso; apply C; reflexivity|].
        split. { exists (T, T + 32). split; [right; left; reflexivity| cbn [fst snd]; lia]. }
        split. { intros b Hb. destruct (APO b ltac:(apply in_or_app; left; exact Hb)) as ((_ & B2 & _) & _). left. lia. }
        split. { intros m1 _ _ _ NM. cbn [app qmain_list]. split; [exact NM| exact I]. }
        reflexivity.
      - destruct (exists_last (l := e0 :: ex0) ltac:(discriminate)) as (exi & el & EEX). unfold tc in *. clear tc. rewrite EEX in *. clear EEX e0 ex0. set (tc := Z.of_nat (length (exi ++ [el]))) in *.
        apply qmain_list_snoc in QE as [QEi (ELc & (ews & EW & LEW & FEW))].
        assert (TCN : tc <> 0) by (subst tc; rewrite length_app; cbn [length]; lia).
        assert (INel : In el (rest ++ exi ++ [el])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
        destruct (APO el INel) as (GEL & APC & APN). pose proof GEL as (GE1 & GE2 & _).
        assert (APE : forall b, In b (rest ++ exi) -> bgeo b /\ (qb_addr AL b + 8192 <= qb_addr AL el \/ qb_addr AL el + 8192 <= qb_addr AL b)).
        { intros b Hb. assert (Hb' : In b (rest ++ exi ++ [el])) by (rewrite app_assoc; apply in_or_app; left; exact Hb).
          destruct (APO b Hb') as (GB & _). split; [exact GB|]. apply (bapart_of b el GB GEL). intros C.
          rewrite app_assoc, map_app in NDr. apply (NoDup_app_disj _ _ (qb_v b) NDr); [apply in_map; exact Hb| rewrite C; left; reflexivity]. }
        exists (qb_addr AL el), (wz (qb_size el)), (wz (qb_count el)).
        split. { intros _. split; [rewrite qlast_snoc; reflexivity| exact ELc]. }
        split. { intros _. fold CA in APC. fold NA in APN. clear - GE1 GE2 APC APN. lia. }
        split. { exists (biv el). split; [| unfold biv; cbn [fst snd]; lia]. right. right. apply in_map. right. right. exact INel. }
        split. { intros b Hb. destruct (APE b ltac:(apply in_or_app; left; exact Hb)) as (_ & A). clear - A. lia. }
        split.
        { intros m1 MU1 WM1 EL1 NM. apply qmain_list_snoc. split; [| exact NM]. apply qmain_list_snoc. split.
          - eapply (qmain_list_frame (W5 (qb_addr AL el)) m m1 exi _ QEi MU1 WM1). apply Forall_forall. intros b Hb.
            destruct (APE b ltac:(apply in_or_app; right; exact Hb)) as ((B1 & B2 & _) & A3).
            destruct (APO b ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & A1 & A2). fold CA in A1. fold NA in A2.
            unfold W5. cbn [disjoint_from]. clear - B1 B2 A1 A2 A3 G0. lia.
          - split; [exact (EL1 TCN)|]. exists ews. split; [| split; [exact LEW| exact FEW]].
            eapply u64arr_transport; [exact EW| exact MU1| exact WM1|]. rewrite LEW. fold CA in APC. fold NA in APN.
            unfold W5. cbn [disjoint_from]. clear - GE1 GE2 APC APN G0. lia. }
        rewrite (proj2 (Z.eqb_neq tc 0) TCN). rewrite (qfirst_app AL (exi ++ [el]) [emptied nx] ltac:(intros C; apply app_eq_nil in C as [_ C]; discriminate)). reflexivity. }
    destruct EXF as (EA & es & ec & ELH & EGH & (ivE & INE & IVE1 & IVE2) & EDJ & EPUSH & EFST).

    assert (GLQ : exists z, In z (cur :: nx :: rest) /\ qlast AL (cur :: nx :: rest) = qb_addr AL z) by apply qlast_in.
    destruct GLQ as (zl & INzl & EGL).
    assert (GZL : bgeo zl) by (apply (proj1 (Forall_forall _ _) FG); destruct INzl as [<-|[<-|Hz]]; [left; reflexivity| right; left; reflexivity| right; right; apply in_or_app; left; exact Hz]).
    pose proof GZL as (GZ1 & GZ2 & _).
    eapply evt_cut.
    { eapply (merge_step G T ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 F fc m CA NA (wz NA)
                (wz (match rest with [] => 0 | b' :: _ => qb_addr AL b' end)) (qb_size cur) (qb_size nx) (qb_count cur) (qb_count nx) cws nws
                gc gf (qlast AL (cur :: nx :: rest)) gb tc (wz (qfirst AL ex)) (wz (qlast AL ex)) (8192 * tc) EA (wz 0) es ec (8192 * tc)
                MI CH CW LCW NH NW LNW GC TC ELH); try exact EGH; try (subst tc CA NA; clear - G0 TH GC1 GC2 GN1 GN2 SEP CS8 NS8 CC1 CC2 NC1 NC2 KM GCR LE QB QR0 EGL GZ1 GZ2; lia). }
    cbv beta. unfold mstep_post.
    intros ms1 (y6 & y7 & y3 & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & CH1 & CW1 & NH1 & NW1 & GC1' & TC1 & EL1).

    fold (W5 EA) in MU1.
    assert (ELN : Z.of_nat (length (ex ++ [emptied nx])) = tc + 1) by (rewrite length_app; cbn [length]; subst tc; lia).
    assert (NM : qb_main m1 (emptied nx) 0).
    { split; [exact NH1|]. exists nws. split; [exact NW1|]. split; [exact LNW| reflexivity]. }
    assert (CM : qb_main m1 (merged cur nx) (match rest with [] => 0 | b' :: _ => qb_addr AL b' end)).
    { split.
      - unfold merged at 2 3. cbn [qb_size]. unfold qb_count at 1. cbn [qb_chunks]. rewrite length_app, Nat2Z.inj_add. exact CH1.
      - exists (copy_into cws (Z.to_nat (qb_count cur)) (firstn (Z.to_nat (qb_count nx)) nws)).
        split; [exact CW1|]. split; [rewrite copy_into_length; exact LCW|].
        unfold merged. cbn [qb_chunks]. unfold qb_count. rewrite !Nat2Z.id, FNW, length_app, map_app, <- FCW.
        rewrite <- (length_map (fun ch => wz (qc_hdr AL ch)) (qb_chunks nx)).
        apply firstn_copy_into. rewrite length_map, LCW. unfold qb_count in KM. clear - KM. lia. }
    assert (RM : qmain_list m1 rest 0).
    { eapply (qmain_list_frame (W5 EA) m m1 rest 0 QL2 MU1 WM1). apply Forall_forall. intros b Hb.
      destruct (APO b ltac:(apply in_or_app; left; exact Hb)) as ((B1 & B2 & _) & A1 & A2). pose proof (EDJ b Hb) as A3.
      unfold W5. cbn [disjoint_from]. clear - B1 B2 A1 A2 A3 G0. lia. }
    apply evt_done. unfold miter_post. cbv zeta. exists y6, y7, y3, y28, y29, y30, m1.
    rewrite ELN. replace (8192 * (tc + 1)) with (8192 * tc + 8192) by lia.
    split; [reflexivity|].
    split.
    { eapply munch_weaken; [| exact MU1]. intros x O. unfold W5. cbn [outside].
      pose proof (outside_In _ x (G, G + 32) O ltac:(left; reflexivity)) as O1.
      pose proof (outside_In _ x (T, T + 32) O ltac:(right; left; reflexivity)) as O2.
      pose proof (outside_In _ x (biv cur) O ltac:(right; right; left; reflexivity)) as O3.
      pose proof (outside_In _ x (biv nx) O ltac:(right; right; right; left; reflexivity)) as O4.
      pose proof (outside_In _ x ivE O INE) as O5. unfold biv in O3, O4. cbn [fst snd] in O1, O2, O3, O4.
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [clear - O5 IVE1 IVE2; lia| exact I]. }
    split; [exact WM1|]. split; [exact MI1|].
    split. { cbn [qmain_list]. split; [exact CM| exact RM]. }
    split. { exact (EPUSH m1 MU1 WM1 EL1 NM). }

    split.
    { assert (EQL : (if qlast AL (cur :: nx :: rest) =? NA then CA else qlast AL (cur :: nx :: rest)) = qlast AL (merged cur nx :: rest)).
      { destruct rest as [|b' r].
        - change (qlast AL [cur; nx]) with NA. rewrite Z.eqb_refl. reflexivity.
        - rewrite !qlast_cons2. destruct (qlast_in b' r) as (z & Hz & EZ). rewrite EZ.
          destruct (APO z ltac:(apply in_or_app; left; exact Hz)) as (_ & _ & A2). fold NA in A2.
          rewrite (proj2 (Z.eqb_neq (qb_addr AL z) NA)) by (clear - A2; lia). reflexivity. }
      rewrite <- EQL. exact GC1'. }
    rewrite qlast_snoc, <- EFST. exact TC1.
  Qed.

  Definition mloop_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (cur nx : qbatch) (rest ex : list qbatch) (gc : Z) (gf gb : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 a3 a4 x28 x29 x30 m',
      let l := fst (q_merge cur (nx :: rest)) in let ex' := ex ++ snd (q_merge cur (nx :: rest)) in
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz G) (wz T) (wz (8192 * Z.of_nat (length ex'))) a3 a4 (wz 1021) (wz (-8192)) (wz 8192)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35710) fc None m' (seg_rom asegs)
      /\ munch ((G, G + 32) :: (T, T + 32) :: map biv (cur :: nx :: rest ++ ex)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ qmain_list m' l 0 /\ qmain_list m' ex' 0
      /\ rw_cells asegs m' G [C8 (wz (gc - Z.of_nat (length (snd (q_merge cur (nx :: rest)))))); C8 gf; C8 (wz (qlast AL l)); C8 gb]
      /\ rw_cells asegs m' T [C8 (wz (Z.of_nat (length ex'))); C8 (wz (qfirst AL ex')); C8 (wz (qlast AL ex')); C8 (wz (8192 * Z.of_nat (length ex')))].

  #[using="G0 TH"] Lemma merge_loop : forall (rest : list qbatch) (cur nx : qbatch) (ex : list qbatch)
      (ra sp gp tp x6 x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (gc : Z) (gf gb : word),
    mem_inv asegs m ->
    qmain_list m (cur :: nx :: rest) 0 -> qmain_list m ex 0 ->
    rw_cells asegs m G [C8 (wz gc); C8 gf; C8 (wz (qlast AL (cur :: nx :: rest))); C8 gb] ->
    rw_cells asegs m T [C8 (wz (Z.of_nat (length ex))); C8 (wz (qfirst AL ex)); C8 (wz (qlast AL ex)); C8 (wz (8192 * Z.of_nat (length ex)))] ->
    Z.of_nat (length rest) + 2 <= gc < 2^63 ->
    List.NoDup (map qb_v (cur :: nx :: rest ++ ex)) -> Forall bgeo (cur :: nx :: rest ++ ex) -> Forall bwf (cur :: nx :: rest) -> Forall bex ex ->
    qbytes (cur :: nx :: rest) < 2^62 -> Z.of_nat (length ex) + Z.of_nat (length rest) + 2 < 2^62 ->
    evt asegs (mloop_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 F fc m cur nx rest ex gc gf gb)
      (MS (mkR ra sp gp tp (wz (qb_addr AL nx)) x6 x7 s0 s1 (wz G) (wz T) (wz (8192 * Z.of_nat (length ex))) a3 (wz (qb_addr AL cur))
               (wz 1021) (wz (-8192)) (wz 8192) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x3562c) fc None m (seg_rom asegs)).
  Proof.
    induction rest as [|nx' rest IH]; intros cur nx ex ra sp gp tp x6 x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m gc gf gb
      MI QL QE GC TC GCR ND FG FW FE QB LE.
    all: pose proof QL as QLc; cbn [qmain_list] in QLc; destruct QLc as ((CH & (cws & CW & LCW & FCW)) & (NH & (nws & NW & LNW & FNW)) & QL2).
    all: pose proof FG as FG'; apply Forall_cons_iff in FG' as [GCU FG']; apply Forall_cons_iff in FG' as [GNX FG'].
    all: pose proof FW as FW'; apply Forall_cons_iff in FW' as [(CS8 & CC1 & CC2) FW']; apply Forall_cons_iff in FW' as [(NS8 & NC1 & NC2) FW'].
    all: pose proof (bwf_qbytes_nonneg _ FW') as QR0; rewrite !qbytes_cons in QB.
    all: assert (VNE : qb_v cur <> qb_v nx) by (cbn [map] in ND; apply NoDup_cons_iff in ND as [NI _]; intros C; apply NI; left; symmetry; exact C).
    all: pose proof (bapart_of cur nx GCU GNX VNE) as SEP; pose proof GCU as (GC1 & GC2 & _); pose proof GNX as (GN1 & GN2 & _).
    all: remember (qb_addr AL cur) as CA eqn:HCA; remember (qb_addr AL nx) as NA eqn:HNA.
    all: do 3 zstep.
    all: zstep; if_cases KM; zify_cond KM.

    -
      do 2 zstep.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; clear - KZ; lia]. clear KZ.
      apply evt_done. unfold mloop_post. rewrite (q_merge_keep cur nx [] ltac:(lia)). cbn [q_merge fst snd length]. rewrite app_nil_r, Z.sub_0_r.
      do 8 eexists. exists m. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
      split; [exact QL|]. split; [exact QE|]. split; [exact GC| exact TC].

    -
      assert (KM' : qb_count cur + qb_count nx <= 1021) by (clear - KM; lia).
      subst CA NA.
      eapply evt_cut.
      { eapply (merge_iter [] cur nx ex ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 F fc m gc gf gb MI QL QE GC TC GCR ND FG FW FE QB LE KM'). }
      cbv beta. unfold miter_post. cbv zeta.
      intros ms1 (y6 & y7 & y3 & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & QL1' & QE1 & GC1' & TC1).
      pose proof QL1' as ((CH1 & _) & _). change (qb_addr AL (merged cur nx)) with (qb_addr AL cur) in CH1.
      remember (qb_addr AL cur) as CA eqn:HCA.
      zstep.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ. lia. } clear KZ.
      apply evt_done. unfold mloop_post. rewrite (q_merge_take cur nx [] KM'). cbn [q_merge fst snd length Z.of_nat Pos.of_succ_nat].
      do 8 eexists. exists m1. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [exact QL1'|]. split; [exact QE1|]. split; [exact GC1'| exact TC1].

    -
      assert (KM' : Q_BATCH < qb_count cur + qb_count nx) by (clear - KM; lia).
      apply Forall_cons_iff in FG' as [GNX' FGr].
      pose proof GNX' as (GX1 & GX2 & _).
      do 2 zstep.
      zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ GX1 GX2 G0 TH. lia. } clear KZ.
      subst CA NA.
      pose proof ND as NDc. cbn [map] in NDc. apply NoDup_cons_iff in NDc as [NI1 NDc].
      pose proof GC as GCc. rewrite qlast_cons2 in GCc.
      pose proof QL as [CM QLt].
      eapply evt_cut.
      { eapply (IH nx nx' ex ra sp gp tp _ _ s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ x31 F fc m gc gf gb MI QLt QE GCc TC);
          [ cbn [length] in GCR; clear - GCR; lia | exact NDc | apply Forall_cons_iff in FG as [_ FG]; exact FG | apply Forall_cons_iff in FW as [_ FW]; exact FW
          | exact FE | clear - QB CS8; rewrite !qbytes_cons; lia | cbn [length] in LE; clear - LE; lia ]. }
      cbv beta. unfold mloop_post. cbv zeta.
      intros ms1 (y5 & y6 & y7 & y3 & y4 & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & QL1' & QE1 & GC1' & TC1).
      apply evt_done. rewrite (q_merge_keep cur nx (nx' :: rest) KM'). cbn [fst snd].
      destruct (q_merge_first (nx' :: rest) nx) as (c' & l' & EL2 & EV2). rewrite EL2 in *.
      exists y5, y6, y7, y3, y4, y28, y29, y30, m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. apply sub_fp_incl. intros iv [<-|[<-|Hin]]; [left; reflexivity| right; left; reflexivity|]. right. right. right. exact Hin. }
      split; [exact WM1|]. split; [exact MI1|].
      split.
      { cbn [qmain_list]. split; [| exact QL1']. rewrite (qb_addr_v c' nx EV2).
        eapply (qb_main_frame _ m m1 cur _ CM MU1 WM1). apply (dj_batches _ cur GCU); [apply Forall_cons_iff in FG as [_ FG]; exact FG| exact NI1]. }
      split; [exact QE1|]. split; [| exact TC1]. rewrite qlast_cons2. exact GC1'.

    -
      assert (KM' : qb_count cur + qb_count nx <= 1021) by (clear - KM; lia).
      apply Forall_cons_iff in FG' as [GNX' FGr].
      pose proof GNX' as (GX1 & GX2 & _).
      subst CA NA.
      eapply evt_cut.
      { eapply (merge_iter (nx' :: rest) cur nx ex ra sp gp tp x7 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x30 x31 F fc m gc gf gb MI QL QE GC TC GCR ND FG FW FE QB LE KM'). }
      cbv beta. unfold miter_post. cbv zeta.
      intros ms1 (y6 & y7 & y3 & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & QL1' & QE1 & GC1' & TC1).
      pose proof QL1' as ((CH1 & _) & _). change (qb_addr AL (merged cur nx)) with (qb_addr AL cur) in CH1.
      remember (qb_addr AL cur) as CA eqn:HCA.
      zstep.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; clear - KZ GX1 GX2 G0 TH; lia]. clear KZ.
      subst CA.
      assert (FGn : Forall bgeo (merged cur nx :: nx' :: rest ++ (ex ++ [emptied nx]))).
      { constructor; [exact GCU|]. apply Forall_cons_iff in FG as [_ FG]. apply Forall_cons_iff in FG as [_ FG].
        rewrite app_assoc. change (Forall bgeo ((nx' :: rest ++ ex) ++ [emptied nx])). apply Forall_app. split; [exact FG| constructor; [exact GNX| constructor]]. }
      assert (NDn : List.NoDup (map qb_v (merged cur nx :: nx' :: rest ++ (ex ++ [emptied nx])))).
      { rewrite app_assoc. change (List.NoDup (qb_v cur :: map qb_v ((nx' :: rest ++ ex) ++ [emptied nx]))). rewrite map_app. cbn [map emptied qb_v].
        eapply Permutation_NoDup; [| exact ND]. cbn [map app]. apply perm_skip. apply (Permutation_cons_append (map qb_v (nx' :: rest ++ ex)) (qb_v nx)). }
      assert (FWn : Forall bwf (merged cur nx :: nx' :: rest)).
      { constructor; [| exact FW']. unfold bwf, merged. cbn [qb_size]. unfold qb_count. cbn [qb_chunks]. rewrite length_app, Nat2Z.inj_add.
        unfold qb_count in CC1, NC1, KM'. clear - CS8 NS8 CC1 NC1 KM'. lia. }
      assert (FEn : Forall bex (ex ++ [emptied nx])) by (apply Forall_app; split; [exact FE| constructor; [split; reflexivity| constructor]]).
      eapply evt_cut.
      { eapply (IH (merged cur nx) nx' (ex ++ [emptied nx]) ra sp gp tp _ _ s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ x31 F fc m1 (gc - 1) gf gb MI1 QL1' QE1 GC1' TC1);
          [ cbn [length] in GCR; clear - GCR; lia | exact NDn | exact FGn | exact FWn | exact FEn
          | clear - QB CS8 NS8; rewrite !qbytes_cons in *; unfold merged; cbn [qb_size]; lia
          | rewrite length_app; cbn [length] in LE |- *; clear - LE; lia ]. }

      cbv beta. unfold mloop_post. cbv zeta.
      intros ms2 (z5 & z6 & z7 & z3 & z4 & z28 & z29 & z30 & m2 & -> & MU2 & WM2 & MI2 & QL2' & QE2 & GC2' & TC2).
      apply evt_done. rewrite (q_merge_take cur nx (nx' :: rest) KM'). cbn [fst snd].
      set (S2 := snd (q_merge (merged cur nx) (nx' :: rest))) in *.
      replace (ex ++ emptied nx :: S2) with ((ex ++ [emptied nx]) ++ S2) by (rewrite <- app_assoc; reflexivity).
      exists z5, z6, z7, z3, z4, z28, z29, z30, m2. split; [reflexivity|].
      split.
      { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. apply sub_fp_incl.
        intros iv [<-|[<-|Hin]]; [left; reflexivity| right; left; reflexivity|]. right. right.
        apply in_map_iff in Hin as (b & <- & Hb).
        destruct Hb as [<-|[<-|Hb]]; [left; reflexivity| right; right; left; reflexivity|].
        apply in_app_or in Hb as [Hb|Hb]; [right; right; right; apply in_map; apply in_or_app; left; exact Hb|].
        apply in_app_or in Hb as [Hb|[<-|[]]]; [right; right; right; apply in_map; apply in_or_app; right; exact Hb| right; left; reflexivity]. }
      split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|]. split; [exact MI2|].
      split; [exact QL2'|]. split; [exact QE2|]. split; [| exact TC2].
      replace (gc - Z.of_nat (length (emptied nx :: S2))) with (gc - 1 - Z.of_nat (length S2)) by (cbn [length]; lia). exact GC2'.
  Qed.

  #[using="Type"] Lemma q_merge_len : forall rest cur, (length (fst (q_merge cur rest)) + length (snd (q_merge cur rest)) = S (length rest))%nat.
  Proof.
    induction rest as [|nx rest IH]; intros cur; [reflexivity|].
    destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
    - rewrite (q_merge_take cur nx rest K). cbn [fst snd length]. specialize (IH (merged cur nx)). lia.
    - rewrite (q_merge_keep cur nx rest K). cbn [fst snd length]. specialize (IH nx). lia.
  Qed.
  #[using="Type"] Lemma q_merge_bytes : forall rest cur, qbytes (fst (q_merge cur rest)) = qbytes (cur :: rest) - 8192 * Z.of_nat (length (snd (q_merge cur rest))).
  Proof.
    induction rest as [|nx rest IH]; intros cur; [cbn [q_merge fst snd length Z.of_nat]; lia|].
    destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
    - rewrite (q_merge_take cur nx rest K). cbn [fst snd length]. rewrite (IH (merged cur nx)), !qbytes_cons. unfold merged. cbn [qb_size]. lia.
    - rewrite (q_merge_keep cur nx rest K). cbn [fst snd]. rewrite !qbytes_cons, (IH nx), qbytes_cons. lia.
  Qed.
  #[using="Type"] Lemma q_merge_ex : forall rest cur, Forall bex (snd (q_merge cur rest)).
  Proof.
    induction rest as [|nx rest IH]; intros cur; [constructor|].
    destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
    - rewrite (q_merge_take cur nx rest K). cbn [snd]. constructor; [split; reflexivity| apply IH].
    - rewrite (q_merge_keep cur nx rest K). cbn [snd]. apply IH.
  Qed.
  #[using="Type"] Lemma qbytes_bex : forall l, Forall bex l -> qbytes l = 8192 * Z.of_nat (length l).
  Proof. induction 1 as [|b l [S8 _] _ IH]; [reflexivity|]. rewrite qbytes_cons, IH, S8. cbn [length]. lia. Qed.

  #[using="Type"] Lemma dj_above : forall L A n, G + 32 <= A -> A + n <= T -> (forall b, In b L -> qb_addr AL b + 8192 <= A) ->
    disjoint_from ((G, G + 32) :: (T, T + 32) :: map biv L) A n.
  Proof.
    intros L A n GA AT HB. cbn [disjoint_from]. split; [lia|]. split; [lia|].
    induction L as [|b L IH]; cbn [map disjoint_from]; [exact I|]. split; [unfold biv; cbn [fst snd]; right; apply HB; left; reflexivity|].
    apply IH. intros b' Hb'. apply HB. right. exact Hb'.
  Qed.
  #[using="Type"] Lemma q_merge_v : forall rest cur b', In b' (fst (q_merge cur rest) ++ snd (q_merge cur rest)) -> In (qb_v b') (map qb_v (cur :: rest)).
  Proof.
    induction rest as [|nx rest IH]; intros cur b' Hin.
    - cbn [q_merge fst snd app] in Hin. destruct Hin as [<-|[]]. left. reflexivity.
    - destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
      + rewrite (q_merge_take cur nx rest K) in Hin. cbn [fst snd] in Hin. apply in_app_or in Hin as [Hin|[<-|Hin]].
        * specialize (IH (merged cur nx) b' ltac:(apply in_or_app; left; exact Hin)). cbn [map merged qb_v] in IH |- *. destruct IH as [E|IH]; [left; exact E| right; right; exact IH].
        * right. left. reflexivity.
        * specialize (IH (merged cur nx) b' ltac:(apply in_or_app; right; exact Hin)). cbn [map merged qb_v] in IH |- *. destruct IH as [E|IH]; [left; exact E| right; right; exact IH].
      + rewrite (q_merge_keep cur nx rest K) in Hin. cbn [fst snd app] in Hin. destruct Hin as [<-|Hin]; [left; reflexivity|]. right. exact (IH nx b' Hin).
  Qed.
  #[using="Type"] Lemma bwf_qbytes_len : forall l, Forall bwf l -> 8192 * Z.of_nat (length l) <= qbytes l.
  Proof. induction 1 as [|b l [S8 _] _ IH]; [cbn; lia|]. rewrite qbytes_cons. cbn [length]. lia. Qed.

  Definition qcells (l : list qbatch) : list cell :=
    [C8 (wz (Z.of_nat (length l))); C8 (wz (qfirst AL l)); C8 (wz (qlast AL l)); C8 (wz (qbytes l))].

  Definition merge_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) (gl : list qbatch) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 m',
      ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((q - 16, q) :: (G, G + 32) :: (T, T + 32) :: map biv gl) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
      /\ qmain_list m' (fst (q_merge_list gl)) 0 /\ qmain_list m' (snd (q_merge_list gl)) 0
      /\ rw_cells asegs m' G (qcells (fst (q_merge_list gl))) /\ rw_cells asegs m' T (qcells (snd (q_merge_list gl))).

  #[using="G0 TH"] Theorem merge_spec : forall (ra gp tp x5 x6 x7 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (gl : list qbatch) (lo q : Z),
    mem_inv asegs m -> stk asegs m lo q -> lo <= q - 16 -> q <= T -> G + 32 <= lo -> (forall b, In b gl -> qb_addr AL b + 8192 <= lo) ->
    qmain_list m gl 0 -> rw_cells asegs m G (qcells gl) -> rw_cells asegs m T (qcells []) ->
    List.NoDup (map qb_v gl) -> Forall bgeo gl -> Forall bwf gl -> qbytes gl < 2^62 -> Z.of_nat (length gl) < 2^62 ->
    evt asegs (merge_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 F fc lo m gl)
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz G) (wz T) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz merge_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp x5 x6 x7 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m gl lo q
      MI ST LOQ QT GLO BLO QL GC TC ND FG FW QB LN.
    unfold merge_entry, qcells in *. cbn [length qfirst qlast qbytes rev fold_right Z.of_nat] in TC.
    pose proof (munch_refl [(q - 16, q); (G, G + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. carve_frame 16%nat ST.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -16) with (q - 16) in * by lia.
    assert (DJF : forall b, In b gl -> disjoint_from [(q - 16, q); (G, G + 32)] (qb_addr AL b) 8192)
      by (intros b Hb; pose proof (BLO b Hb); pose proof (proj1 (Forall_forall _ _) FG b Hb) as (B1 & _); cbn [disjoint_from]; lia).
    assert (QLA : qmain_list mA gl 0) by (eapply (qmain_list_frame _ m mA gl 0 QL MU WM); apply Forall_forall; exact DJF).

    assert (EXIT2 : forall y5 y4 : word, q_merge_list gl = (gl, []) ->
              evt asegs (merge_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x31 F fc lo m gl)
                (MS (mkR ra (wz (q - 16)) gp tp y5 x6 x7 s0 s1 (wz G) (wz T) a2 a3 y4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz 0x35728) fc None mA (seg_rom asegs))).
    { intros y5 y4 EQ.
      do 3 zstep.
      zstep.
      zstep. replace (q - 16 + 16) with q by lia. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      release_frame FR ST q.
      pose proof (bwf_qbytes_nonneg gl FW) as QB0.
      rewrite Z.mod_small, Z.sub_0_r in GC by (clear - QB QB0; lia).
      assert (QLB : qmain_list mB gl 0) by (eapply (qmain_list_frame _ m mB gl 0 QL MU WM); apply Forall_forall; exact DJF).
      apply evt_done. unfold merge_post, qcells. rewrite EQ. cbn [fst snd length qfirst qlast qbytes rev fold_right Z.of_nat].
      do 13 eexists. exists mB. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. apply sub_fp_incl. intros iv [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]. }
      split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact QLB|]. split; [exact I|]. split; [exact GC| exact TC]. }

    zstep.
    zstep. if_cases K1; zify_cond K1.
    {
      destruct gl as [|b r]; [apply EXIT2; reflexivity|]. exfalso.
      apply Forall_cons_iff in FG as [(B1 & B2 & _) _]. cbn [qfirst] in K1. rewrite Z.mod_small in K1 by (clear - B1 B2 G0 TH; lia). clear - K1 B1 G0. lia. }
    destruct gl as [|b r]; [exfalso; apply K1; reflexivity|]. clear K1.
    pose proof QLA as [(BH & _) _]. cbn [qfirst] in *.
    pose proof FG as FGc. apply Forall_cons_iff in FGc as [(B1 & B2 & _) FGr].
    remember (qb_addr AL b) as BA eqn:HBA.
    zstep.
    zstep. if_cases K2; zify_cond K2.
    {
      destruct r as [|nx rest]; [subst BA; apply EXIT2; reflexivity|]. exfalso.
      apply Forall_cons_iff in FGr as [(N1 & N2 & _) _]. rewrite Z.mod_small in K2 by (clear - N1 N2 G0 TH; lia). clear - K2 N1 G0. lia. }
    destruct r as [|nx rest]; [exfalso; apply K2; reflexivity|]. clear K2.
    do 5 zstep.
    subst BA.

    eapply evt_cut.
    { eapply (merge_loop rest b nx [] ra (wz (q - 16)) gp tp _ _ s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ x31 F fc mA
                (Z.of_nat (length (b :: nx :: rest))) (wz (qb_addr AL b)) (wz (qbytes (b :: nx :: rest))));
        [ assumption | exact QLA | exact I | exact GC | exact TC | cbn [length] in LN |- *; clear - LN; lia
        | rewrite app_nil_r; exact ND | rewrite app_nil_r; exact FG | exact FW | constructor | exact QB | cbn [length] in LN |- *; clear - LN; lia ]. }
    cbv beta. unfold mloop_post. cbv zeta. cbn [app].
    set (LL := fst (q_merge b (nx :: rest))) in *. set (EX := snd (q_merge b (nx :: rest))) in *.
    intros ms1 (y5 & y6 & y7 & y3 & y4 & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & QL1 & QE1 & GC1 & TC1).
    rewrite app_nil_r in MU1.
    assert (BLO' : forall b0, In b0 (b :: nx :: rest) -> qb_addr AL b0 + 8192 <= q - 16) by (intros b0 Hb0; pose proof (BLO b0 Hb0); lia).
    assert (BLO'' : forall b0, In b0 (b :: nx :: rest) -> qb_addr AL b0 + 8192 <= lo) by exact BLO.
    eapply (rw_cells_transport asegs _ mA m1) in FR; [| exact MU1| exact WM1| cbn [cells_size csize Nat.add]; apply (dj_above _ (q - 16) 16); [clear - GLO LOQ; lia| clear - QT; lia| exact BLO']].
    eapply (stk_transport_disjoint asegs _ mA m1) in ST; [| exact MU1| exact WM1| apply (dj_above _ lo (q - 16 - lo)); [exact GLO| clear - QT; lia| exact BLO'']].
    pose proof (munch_refl [(q - 16, q); (G, G + 32)] m1) as MUx. pose proof (wmono_refl asegs m1) as WMx.
    do 3 zstep.
    zstep.
    zstep. replace (q - 16 + 16) with q by lia. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
    release_frame FR ST q.

    assert (EBY : Z_to_bv 64 (qbytes (b :: nx :: rest) mod 18446744073709551616 - (8192 * Z.of_nat (length EX)) mod 18446744073709551616) = wz (qbytes LL)).
    { apply Z_to_bv_eqm. change (2^64) with 18446744073709551616. rewrite <- Zminus_mod. f_equal. unfold LL, EX. rewrite (q_merge_bytes (nx :: rest) b). reflexivity. }
    assert (ECN : Z.of_nat (length (b :: nx :: rest)) - Z.of_nat (length EX) = Z.of_nat (length LL)).
    { pose proof (q_merge_len (nx :: rest) b) as QLN. fold LL EX in QLN. cbn [length] in QLN |- *. lia. }
    assert (EFS : qb_addr AL b = qfirst AL LL).
    { destruct (q_merge_first (nx :: rest) b) as (c' & l' & E1 & E2). fold LL in E1. rewrite E1. cbn [qfirst]. symmetry. apply qb_addr_v. exact E2. }
    rewrite EBY, ECN, EFS in GC1.
    rewrite <- (qbytes_bex EX (q_merge_ex (nx :: rest) b)) in TC1.
    assert (DJR : forall b', In b' (LL ++ EX) -> disjoint_from [(q - 16, q); (G, G + 32)] (qb_addr AL b') 8192).
    { intros b' Hb'. pose proof (q_merge_v (nx :: rest) b b' Hb') as HV. apply in_map_iff in HV as (b0 & EV & Hb0).
      rewrite (qb_addr_v b' b0 (eq_sym EV)). pose proof (BLO b0 Hb0). pose proof (proj1 (Forall_forall _ _) FG b0 Hb0) as (B01 & _). cbn [disjoint_from]. lia. }
    assert (QLB : qmain_list mB LL 0).
    { eapply (qmain_list_frame _ m1 mB LL 0 QL1 MUx WMx). apply Forall_forall. intros b' Hb'. apply DJR. apply in_or_app. left. exact Hb'. }
    assert (QEB : qmain_list mB EX 0).
    { eapply (qmain_list_frame _ m1 mB EX 0 QE1 MUx WMx). apply Forall_forall. intros b' Hb'. apply DJR. apply in_or_app. right. exact Hb'. }
    apply evt_done. unfold merge_post, qcells. cbn [q_merge_list]. fold LL EX.
    do 13 eexists. exists mB. split; [reflexivity|].
    split.
    {
      eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU1]]; apply sub_fp_incl.
      - intros iv [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity].
      - intros iv Hin. right. exact Hin. }
    split; [exact (wmono_trans asegs _ _ _ WM WM1)|]. split; [assumption|]. split; [exact ST|].
    split; [exact QLB|]. split; [exact QEB|]. split; [exact GC1| exact TC1].
  Qed.

  Definition bshadow (m : mem) (b : qbatch) : Prop := rw_cells asegs m (sh (qb_addr AL b)) [CB 1024 (fa_bytes 1024)].
  #[using="Type"] Lemma qlist_rep_main : forall m l nxt, qlist_rep AL m l nxt <-> qmain_list m l nxt /\ Forall (bshadow m) l.
  Proof.
    intros m l nxt. induction l as [|b l IH]; cbn [qlist_rep qmain_list].
    - split; [intros _; split; [exact I| constructor]| intros _; exact I].
    - rewrite IH. unfold qbatch_rep, qb_main, bshadow. split.
      + intros ((R1 & R2 & R3) & QM & FS). split; [split; [split; assumption| exact QM]| constructor; assumption].
      + intros (((R1 & R2) & QM) & FS). apply Forall_cons_iff in FS as [R3 FS]. split; [split; [exact R1| split; [exact R2| exact R3]]| split; assumption].
  Qed.
End MERGE.

