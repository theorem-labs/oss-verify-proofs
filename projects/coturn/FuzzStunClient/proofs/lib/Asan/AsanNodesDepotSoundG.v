(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 DepotInvG AxPriv AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesPG AsanNodesPGSoundG AsanNodesDepot.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWordLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ImgZero.
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
Definition put_clob (r : bv 5) : Prop :=
  r = 5%bv \/ r = 6%bv \/ r = 10%bv \/ r = 11%bv \/ r = 12%bv \/ r = 13%bv \/ r = 14%bv \/ r = 15%bv \/ r = 16%bv.

Definition put_specG (SEGS : list Segment) (DP SB IH : Z) : Prop :=
  forall (mem rom : word -> option byte) (usp T w size tag : Z) (bs : list byte) (ret : word)
         (B P ncap fcap k : Z) (regs : bvmap 5 word),
    depot_invG SEGS DP SB IH B P ncap fcap (k + 1) mem -> 0 <= k ->
    2 ^ 32 <= usp - 224 -> usp < 2 ^ 64 -> okrG SEGS mem (usp - 224) 224 ->
    2 ^ 32 <= T -> T + 8 * size < 2 ^ 64 ->
    rdn SEGS mem (Z_to_bv 64 T) (Z.to_nat (8 * size)) = Some bs ->
    (T + 8 * size <= usp - 224 \/ usp <= T) ->
    w = size + tag * 2 ^ 32 -> 1 <= size <= 255 -> 0 <= tag < 256 ->
    (usp <= B \/ B + 16 * ncap <= usp - 224) -> (usp <= P \/ P + 8 * fcap <= usp - 224) ->
    (T + 8 * size <= B \/ B + 16 * ncap <= T) -> (T + 8 * size <= P \/ P + 8 * fcap <= T) ->
    ret_ok ret ->
    getr regs 1%bv = ret -> getr regs 2%bv = Z_to_bv 64 usp -> getr regs 10%bv = Z_to_bv 64 T -> getr regs 11%bv = Z_to_bv 64 w ->
    exists (regs' : bvmap 5 word) (mem' : word -> option byte) (id : Z),
         msteps SEGS (mkst regs (Z_to_bv 64 (DPN.put_entry_of IH)) mem rom) (mkst regs' ret mem' rom)
      /\ depot_invG SEGS DP SB IH B P ncap fcap k mem'
      /\ getr regs' 10%bv = Z_to_bv 64 id /\ 0 <= id < ncap
      /\ getr regs' 2%bv = Z_to_bv 64 usp /\ getr regs' 1%bv = ret
      /\ (forall r, ~ put_clob r -> getr regs' r = getr regs r)
      /\ (forall x : word, ~ (usp - 224 <= bv_unsigned x < usp) -> ~ depot_footG DP SB B P ncap fcap (bv_unsigned x) -> mem' x = mem x)
      /\ mem_grows mem mem'.

(* [comment removed for export] *)




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
Hypothesis SEGS_wr : segs_wr_ok SEGS.
(* [comment removed for export] *)
Variables DP SB IH : Z.
Hypothesis LAYOUT : 2 ^ 16 <= DP /\ DP + 4194328 <= IH /\ 2 ^ 16 <= SB /\ SB + 28 <= IH /\ IH < 2 ^ 32 /\ (DP + 4194328 <= SB \/ SB + 28 <= DP).
(* [comment removed for export] *)
Hypothesis IMG0 : forall x : word, DP <= bv_unsigned x < DP + 4194304 -> seg_rom SEGS x = Some (Z_to_bv 8 0).
Hypothesis PSPEC : put_specG SEGS DP SB IH.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma havoc_rs_sound : forall E rs k M M',
  know_ok SEGS E M k -> mem_grows M M' ->
  (forall x : word, ~ in_rs E rs (bv_unsigned x) -> M' x = M x) ->
  know_ok SEGS E M' (DPN.havoc_rs k rs).
Proof.
  intros E rs. induction rs as [|r rest IHl]; intros k M M' HK GR FR; cbn [DPN.havoc_rs].
  - assert (EQ : M' = M).
    { apply functional_extensionality. intros x. apply FR. intros H. apply Exists_nil in H. exact H. }
    rewrite EQ. exact HK.
  - set (inr := fun x : word => ((pstart E (fst r) <=? bv_unsigned x) && (bv_unsigned x <? pstart E (fst r) + pvE E (snd r)))%bool).
    set (M1 := fun x : word => if inr x then M' x else M x).
    apply (IHl _ M1 M').
    + destruct r as [[rb rk] rl]. cbn [fst snd a_base a_off].
      eapply w_know_ok_havoc; [exact HK | |].
      * intros x Hx. unfold M1, inr. cbn [fst snd].
        replace (estart E (SA rb rk)) with (pstart E (SA rb rk)) in Hx by reflexivity.
        replace (elenZ E rl) with (pvE E rl) in Hx by reflexivity.
        destruct (Z.leb_spec (pstart E (SA rb rk)) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (pstart E (SA rb rk) + pvE E rl)); cbn [andb]; try reflexivity. lia.
      * intros x Hx. unfold M1. destruct (inr x); [apply GR; exact Hx | exact Hx].
    + intros x Hx. unfold M1 in Hx. destruct (inr x); [exact Hx | apply GR; exact Hx].
    + intros x Hnot. unfold M1. destruct (inr x) eqn:Hin; [reflexivity|]. apply FR. intros HE.
      apply Exists_cons in HE as [H1|H2]; [|exact (Hnot H2)].
      unfold inr in Hin. destruct (Z.leb_spec (pstart E (fst r)) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (pstart E (fst r) + pvE E (snd r))); cbn [andb] in Hin; try discriminate; lia.
Qed.

Lemma kn_vars_lt_in : forall b k K, AP.kn_vars_lt b k = true -> In K k -> AP.kentry_vars_lt b K = true.
Proof.
  induction k as [|K' rest IHl]; intros K H Hin; [destruct Hin|]. cbn [AP.kn_vars_lt] in H.
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1 | exact (IHl K H2 Hin)].
Qed.

(* [comment removed for export] *)
Lemma tok_lits_some : forall args nc fc dp sb ih,
  DPN.tok_lits args = Some (nc, fc, dp, sb, ih) -> exists eB eP, args = [eB; eP; ELit nc; ELit fc; ELit dp; ELit sb; ELit ih].
Proof.
  intros args nc fc dp sb ih H. unfold DPN.tok_lits in H.
  repeat match type of H with context [match ?e with _ => _ end] => destruct e; try discriminate H end.
  injection H as <- <- <- <- <-. eexists _, _. reflexivity.
Qed.

Lemma find_token_in : forall k rs args nc fc kk,
  DPN.find_token DP SB IH k = Some (rs, args, nc, fc, kk) ->
  In (KPriv 0 rs args kk) k
  /\ exists r1 r2 r3 r4 eB eP, rs = [r1; r2; r3; r4] /\ args = [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH].
Proof.
  induction k as [|K rest IHl]; intros rs args nc fc kk H; [discriminate|].
  cbn [DPN.find_token] in H.
  assert (REST : DPN.find_token DP SB IH rest = Some (rs, args, nc, fc, kk) ->
            In (KPriv 0 rs args kk) (K :: rest) /\
            exists r1 r2 r3 r4 eB eP, rs = [r1; r2; r3; r4] /\ args = [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH]).
  { intros H'. destruct (IHl _ _ _ _ _ H') as [Hin Hex]. split; [right; exact Hin | exact Hex]. }
  destruct K as [| | | | | | | | | |pt prs pargs pk]; try (apply REST; exact H).
  destruct pt; [|apply REST; exact H].
  destruct prs as [|r1 [|r2 [|r3 [|r4 [|? ?]]]]]; try (apply REST; exact H).
  destruct (DPN.tok_lits pargs) as [[[[[nc' fc'] dp] sb] ih]|] eqn:Htl; [|apply REST; exact H].
  destruct (Z.eqb dp DP && Z.eqb sb SB && Z.eqb ih IH)%bool eqn:Hl; [|apply REST; exact H].
  apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst dp sb ih.
  injection H as <- <- <- <- <-. split; [left; reflexivity|].
  destruct (tok_lits_some _ _ _ _ _ _ Htl) as (eB & eP & ->). exists r1, r2, r3, r4, eB, eP. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma split_lit_val : forall E e b o lo,
  split_lit e = (b, o) -> lo <= bv_unsigned (edenot E e) -> 0 < lo ->
  0 <= bv_unsigned (edenot E b) + o -> bv_unsigned (edenot E b) + o <= 2 ^ 64 ->
  bv_unsigned (edenot E e) = bv_unsigned (edenot E b) + o.
Proof.
  intros E e b o lo Hs Hlo Hlo0 H0 H64.
  rewrite (split_lit_denot E e b o Hs) in Hlo |- *.
  destruct (Z.eq_dec (bv_unsigned (edenot E b) + o) (2 ^ 64)) as [EQ|NE].
  - exfalso. rewrite EQ in Hlo. rewrite Z_to_bv_unsigned, bv_wrap64_mod in Hlo. rewrite Z.mod_same in Hlo by lia. lia.
  - rewrite u64_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma okr_of_store_ok : forall M a n,
  0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> 0 <= n ->
  store_ok SEGS M (Z_to_bv 64 a) (Z.to_nat n) = true -> okrG SEGS M a n.
Proof.
  intros M a n Ha Han Hn H j Hj.
  pose proof (store_ok_all SEGS M (Z.to_nat n) (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) H
                (Z_to_bv 64 (a + j)) ltac:(rewrite !u64_lit by lia; rewrite Z2Nat.id by lia; lia)) as X.
  cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 (a + j))); [reflexivity | exfalso; exact (X eq_refl)].
Qed.

Lemma store_ok_prefix : forall M a n n',
  0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> 0 <= n' <= n ->
  store_ok SEGS M (Z_to_bv 64 a) (Z.to_nat n) = true -> store_ok SEGS M (Z_to_bv 64 a) (Z.to_nat n') = true.
Proof.
  intros M a n n' Ha Han Hn H. apply store_ok_of_all; [rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. rewrite Z2Nat.id in Hx by lia.
  eapply (store_ok_all SEGS M (Z.to_nat n) (Z_to_bv 64 a)); [rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia | exact H |].
  rewrite u64_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma not_put_clob : forall r : bv 5, r <> 0%bv -> ~ In (ridx r) DPN.PUT_REGS -> ~ put_clob r.
Proof.
  intros r Hr0 Hnot HC. apply Hnot. unfold put_clob in HC. unfold DPN.PUT_REGS.
  destruct HC as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbv; auto 12.
Qed.

Theorem node_put_sound : forall args0,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => DPN.node_put nx0 DP SB IH cs args0).
Proof.
  intros args0 cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold DPN.node_put, DPN.put_tests in Hn. destruct args0; [|discriminate].
  destruct (reg cs 1) as [ret| | | | | | |] eqn:Hr1; try discriminate.
  destruct (DPN.find_token DP SB IH (kn cs)) as [[[[[rs args] nc] fc] kk]|] eqn:Htok; [|discriminate].
  destruct (split_lit (reg cs 2)) as [sb so] eqn:Hsp.
  destruct (split_lit (reg cs 10)) as [tb to] eqn:Htr.
  destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [tlo|] eqn:Htlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [thi|] eqn:Hthi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 11)) as [zlo|] eqn:Hzlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [zhi|] eqn:Hzhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  cbn [forallb andb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hfresh Hvtok Hvsb HArs HArsS HAts Htw Hzhi255 Hzlo1 Hthi64 Htlo32 Hsw HsloB Hfc Hnc Hkk1 Hret2 Hret64 Hret0 Hpc. clear Hall.
  apply Z.eqb_eq in Hpc. apply Z.leb_le in Hret0. apply Z.ltb_lt in Hret64. apply Z.eqb_eq in Hret2.
  apply Z.leb_le in Hkk1. apply andb_prop in Hnc as [Hnc2 Hnc16]. apply Z.leb_le in Hnc2. apply Z.leb_le in Hnc16.
  apply andb_prop in Hfc as [Hfc1 Hfc2]. apply Z.leb_le in Hfc1. apply Z.leb_le in Hfc2.
  apply Z.leb_le in HsloB. apply Z.leb_le in Htlo32. apply Z.ltb_lt in Hthi64. apply Z.leb_le in Hzlo1. apply Z.leb_le in Hzhi255.
  unfold two64 in Hret64, Hthi64. unfold two32z in HsloB, Htlo32. unfold DPN.SCRATCH in *.
  injection Hn as <-.
  assert (LL : 0 <= DP < 2 ^ 64 /\ 0 <= SB < 2 ^ 64 /\ 0 <= IH < 2 ^ 64) by lia. destruct LL as (LDP & LSB & LIH).
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 1 HC ltac:(lia)) as R1.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  rewrite Hr1 in R1. cbn [edenot] in R1.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hslo) as Bslo.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Htlo) as Btlo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hthi) as Bthi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hzlo) as Bzlo.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hzhi) as Bzhi.
  set (usp := bv_unsigned (edenot E (reg cs 2))) in *.
  set (T := bv_unsigned (edenot E (reg cs 10))) in *.
  set (size := bv_unsigned (edenot E (reg cs 11))) in *.
  pose proof (u64_range (edenot E (reg cs 2))) as Uusp. pose proof (u64_range (edenot E (reg cs 10))) as UT.
  pose proof (u64_range (edenot E (reg cs 11))) as Usize. fold usp in Uusp. fold T in UT. fold size in Usize.
  (* [comment removed for export] *)
  destruct (find_token_in (kn cs) rs args nc fc kk Htok) as (Hin & r1 & r2 & r3 & r4 & eB & eP & -> & ->).
  pose proof (proj1 (Forall_forall _ _) HKN _ Hin) as HT. cbn [kentry_ok] in HT. destruct HT as [Hflat HP].
  cbn [PRIV] in HP. rewrite !pvE_lit in HP by lia.
  destruct HP as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & L4 & HI).
  set (B := pvE E eB) in *. set (P := pvE E eP) in *.
  (* [comment removed for export] *)
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) sb (so - 224) 224 HKN HKN Hsw ltac:(lia)) as (Sscr & Sscr0 & Sscr64).
  unfold estart in Sscr, Sscr0, Sscr64. cbn [a_base a_off] in Sscr, Sscr0, Sscr64.
  assert (Husp : usp = bv_unsigned (edenot E sb) + so).
  { apply (split_lit_val E (reg cs 2) sb so slo Hsp Bslo); lia. }
  assert (OKS : okrG SEGS M (usp - 224) 224).
  { apply okr_of_store_ok; [lia | lia | lia |]. replace (usp - 224) with (bv_unsigned (edenot E sb) + (so - 224)) by lia. exact Sscr. }
  (* [comment removed for export] *)
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) tb to (8 * zhi) HKN HKN Htw ltac:(lia)) as (Str & Str0 & Str64).
  unfold estart in Str, Str0, Str64. cbn [a_base a_off] in Str, Str0, Str64.
  assert (HT : T = bv_unsigned (edenot E tb) + to).
  { apply (split_lit_val E (reg cs 10) tb to tlo Htr Btlo); lia. }
  assert (StrS : store_ok SEGS M (Z_to_bv 64 T) (Z.to_nat (8 * size)) = true).
  { rewrite HT. apply (store_ok_prefix M _ (8 * zhi)); [lia | lia | lia | exact Str]. }
  destruct (store_ok_rdn SEGS SEGS_wr (Z.to_nat (8 * size)) M (Z_to_bv 64 T) ltac:(rewrite u64_lit by lia; rewrite Z2Nat.id by lia; lia) StrS)
    as (bs & Hrd & Hlen).
  (* [comment removed for export] *)
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN HAts) as Dts.
  unfold estart in Dts. cbn [a_base a_off] in Dts. rewrite !elenZ_lit in Dts by lia.
  unfold DPN.apart_rs in HArs, HArsS. cbn [forallb fst snd] in HArs, HArsS.
  apply andb_prop in HArs as [_ HArs]. apply andb_prop in HArs as [Ds2 HArs]. apply andb_prop in HArs as [_ HArs]. apply andb_prop in HArs as [Ds4 _].
  apply andb_prop in HArsS as [_ HArsS]. apply andb_prop in HArsS as [Dt2 HArsS]. apply andb_prop in HArsS as [_ HArsS]. apply andb_prop in HArsS as [Dt4 _].
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ds2) as Ds2'.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Ds4) as Ds4'.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Dt2) as Dt2'.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Dt4) as Dt4'.
  clear Ds2 Ds4 Dt2 Dt4.
  rewrite !elenZ_lit in Ds2', Ds4', Dt2', Dt4' by lia.
  assert (EST : forall a : saddr, estart E (SA (a_base a) (a_off a)) = pstart E a) by (intros [? ?]; reflexivity).
  rewrite !EST in Ds2', Ds4', Dt2', Dt4'.
  change (elenZ E (snd r2)) with (pvE E (snd r2)) in Ds2', Dt2'. change (elenZ E (snd r4)) with (pvE E (snd r4)) in Ds4', Dt4'.
  unfold estart in Ds2', Ds4', Dt2', Dt4'. cbn [a_base a_off] in Ds2', Ds4', Dt2', Dt4'.
  rewrite A2, L2 in Ds2', Dt2'. rewrite A4, L4 in Ds4', Dt4'.
  (* [comment removed for export] *)
  assert (Hret : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by lia; exact Hret2).
  replace kk with (kk - 1 + 1) in HI by lia.
  destruct (PSPEC M (seg_rom SEGS) usp T size size 0 bs (Z_to_bv 64 ret) B P nc fc (kk - 1) R HI ltac:(lia) ltac:(lia) ltac:(lia) OKS
             ltac:(lia) ltac:(lia) Hrd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
             R1 ltac:(unfold usp; rewrite Z_to_bv_bv_unsigned; exact R2) ltac:(unfold T; rewrite Z_to_bv_bv_unsigned; exact R10)
             ltac:(replace (size + 0 * 2 ^ 32) with size by lia; unfold size; rewrite Z_to_bv_bv_unsigned; exact R11))
    as (regs' & M' & id & Hms & HI' & R10' & Hid & R2' & R1' & RR & FR & GR).
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (nx := nxt cs) in *.
  pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HREG.
  rewrite <- Hpc in Hms.
  (* [comment removed for export] *)
  set (E' := ext_list E nx (map (fun r => getr regs' (Z_to_bv 5 (Z.of_nat r))) DPN.PUT_REGS)).
  assert (Hag : env_agree nx E E') by (unfold E'; apply ext_list_agree).
  assert (HR2 : regs_ok E' (sr_fresh (s_regs (a_ss cs)) DPN.PUT_REGS nx) regs').
  { unfold E'. apply (regs_ok_region DPN.PUT_REGS E (s_regs (a_ss cs)) R regs' nx HREG Fsr).
    - unfold DPN.PUT_REGS. repeat constructor.
    - intros r Hr0 Hnot. apply RR. exact (not_put_clob r Hr0 Hnot). }
  assert (HEid : ev E' nx = Z_to_bv 64 id).
  { unfold E'. replace nx with (nx + N.of_nat 0)%N at 2 by lia. rewrite ext_list_at by (cbn; lia). cbn [map nth DPN.PUT_REGS]. exact R10'. }
  (* [comment removed for export] *)
  assert (Esb : edenot E' sb = edenot E sb) by (symmetry; exact (edenot_agree' nx E E' sb Hag Hvsb)).
  cbn [APC.kentry_vars_lt forallb APC.sr_vars_lt] in Hvtok.
  apply andb_prop in Hvtok as [_ Hva]. apply andb_prop in Hva as [HveB Hva]. apply andb_prop in Hva as [HveP _].
  assert (EeB : pvE E' eB = B) by (unfold B, pvE; rewrite <- (edenot_agree' nx E E' eB Hag HveB); reflexivity).
  assert (EeP : pvE E' eP = P) by (unfold P, pvE; rewrite <- (edenot_agree' nx E E' eP Hag HveP); reflexivity).
  (* [comment removed for export] *)
  pose proof (know_ok_agree' SEGS nx E E' M [KPriv 0 [r1; r2; r3; r4] [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH] kk] Hag) as HT'.
  cbn [AP.kn_vars_lt] in HT'.
  specialize (HT' ltac:(rewrite andb_true_r; eapply kn_vars_lt_in; [exact Fkn | exact Hin]) ltac:(constructor; [exact (proj1 (Forall_forall _ _) HKN _ Hin) | constructor])).
  apply Forall_inv in HT'. cbn [kentry_ok] in HT'. destruct HT' as [Hflat' HP']. cbn [PRIV] in HP'. rewrite !pvE_lit in HP' by lia.
  rewrite EeB, EeP in HP'.
  destruct HP' as (A1' & L1' & A2' & L2' & A3' & L3' & A4' & L4' & _).
  (* [comment removed for export] *)
  assert (HK2 : know_ok SEGS E' M' (DPN.put_kn (kn cs) sb so [r1; r2; r3; r4] [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH] kk nc nx)).
  { unfold DPN.put_kn. constructor; [|constructor].
    - (* [comment removed for export] *)
      cbn [kentry_ok]. split; [exact Hflat'|]. cbn [PRIV]. rewrite !pvE_lit by lia. rewrite EeB, EeP.
      repeat (split; [assumption|]). exact HI'.
    - (* [comment removed for export] *)
      cbn [kentry_ok edenot]. rewrite HEid. rewrite u64_lit by lia. lia.
    - (* [comment removed for export] *)
      apply (havoc_rs_sound E' _ (DPN.drop_tokens (kn cs)) M M').
      + unfold DPN.drop_tokens. apply know_ok_filter. eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
      + exact GR.
      + intros x Hx. apply FR.
        * intros Hs. apply Hx. unfold in_rs. apply Exists_cons_hd. cbn [fst snd]. unfold pstart, pvE. cbn [a_base a_off edenot].
          unfold DPN.SCRATCH. rewrite Esb. rewrite u64_lit by lia. lia.
        * intros Hf. apply Hx. unfold in_rs. apply Exists_cons_tl. unfold depot_footG in Hf.
          destruct Hf as [Hf|[Hf|[Hf|Hf]]];
            [ apply Exists_cons_hd
            | apply Exists_cons_tl, Exists_cons_hd
            | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd
            | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd ]; lia. }
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree nx0_ge7 FS0
            cs E E' R FULL model TT ret _ _ (nx + 9)%N regs' M' HC Hfresh Hag Hms HR2 HK2).
  intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
  split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kreadn_rdn : forall E M k b off n v,
  know_ok SEGS E M k -> DPN.kreadn SEGS k b off n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b off) (Z.of_nat n) ->
  exists bs, rdn SEGS M (Z_to_bv 64 (estart E (SA b off))) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros E M k b off n v HK H Hn1 Hn8 Hfl. unfold DPN.kreadn in H.
  pose proof (know_lookup_sound SEGS E M k b off n false [] [] HK Hn1 Hn8) as Hs.
  destruct (know_lookup SEGS k b off n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & P1 & P2 & P3). unfold extz in P3.
  exists bs. rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E (SA b off))) in P1. rewrite (flat_u E _ _ Hfl) in P1.
  split; [exact P1 | split; [exact P2 | exact P3]].
Qed.

Lemma klit_cell : forall E M k b off n z,
  know_ok SEGS E M k -> DPN.klit SEGS k b off n = Some z -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b off) (Z.of_nat n) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  cellG SEGS M n (estart E (SA b off)) z.
Proof.
  intros E M k b off n z HK H Hn1 Hn8 Hfl Hz. unfold DPN.klit in H.
  destruct (DPN.kreadn SEGS k b off n) as [[z'| | | | | | |]|] eqn:Hr; try discriminate. injection H as ->.
  destruct (kreadn_rdn E M k b off n (ELit z) HK Hr Hn1 Hn8 Hfl) as (bs & P1 & P2 & P3). cbn [edenot] in P3.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite P2 in Hb.
  assert (H64 : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (EQ : bytes_le_to_Z bs = z).
  { apply (f_equal bv_unsigned) in P3. rewrite !u64_lit in P3 by lia. exact P3. }
  split; [|lia]. rewrite P1. f_equal. unfold word_to_le_bytes. rewrite u64_lit by lia. rewrite <- EQ, <- P2.
  symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma rdn_none_img : forall n M a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat n -> M (Z_to_bv 64 (a + j)) = None /\ seg_rom SEGS (Z_to_bv 64 (a + j)) = Some (Z_to_bv 8 0)) ->
  rdn SEGS M (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  induction n as [|n IHn]; intros M a Ha Hn H; [reflexivity|].
  cbn [rdn repeat]. destruct (H 0 ltac:(lia)) as [M0 R0]. rewrite Z.add_0_r in M0, R0. rewrite M0, R0.
  rewrite zbv_add1. rewrite (IHn M (a + 1)); [reflexivity | lia | lia |].
  intros j Hj. replace (a + 1 + j) with (a + (1 + j)) by lia. apply H. lia.
Qed.

Lemma reach_cover : forall ps fuel cur x,
  DPN.reach DP ps cur fuel = true -> cur <= x < DP + DPN.TABSZ ->
  exists s e v, In (s, e, v) ps /\ s <= x < e.
Proof.
  induction fuel as [|f IHf]; intros cur x H Hx; [discriminate|]. cbn [DPN.reach] in H.
  destruct (Z.leb (DP + DPN.TABSZ) cur) eqn:Hend; [apply Z.leb_le in Hend; lia|].
  destruct (find _ ps) as [[[s e] v]|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin Hc]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Z_lt_le_dec x e); [exists s, e, v; split; [exact Hin | lia] | exact (IHf e x H ltac:(lia))].
Qed.

Lemma tab_pieces_in : forall k s e v, In (s, e, v) (DPN.tab_pieces DP k) ->
  DP <= s /\ e <= DP + DPN.TABSZ /\
  ((v = None /\ exists lo hi, In (KImg lo hi) k /\ lo <= s /\ e <= hi)
   \/ (exists z, v = Some z /\ e = s + 4 /\ In (KWord (SA (ELit 0) s) 4 (ELit z)) k)).
Proof.
  intros k s e v H. unfold DPN.tab_pieces in H. apply in_flat_map in H as (K & HK & Hp).
  destruct K as [[b o] w v'|[b o] nn|[b o] nn kb|ilo ihi|e' m|e' rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn |pt prs pargs pk];
    try (destruct Hp; fail).
  - (* [comment removed for export] *) destruct b as [bz| | | | | | |]; try (destruct Hp; fail). destruct bz; try (destruct Hp; fail).
    destruct v' as [z| | | | | | |]; try (destruct Hp; fail).
    destruct (Nat.eqb w 4 && Z.leb DP o && Z.leb (o + 4) (DP + DPN.TABSZ))%bool eqn:C; [|destruct Hp].
    apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. first [apply Nat.eqb_eq in C1 | apply N.eqb_eq in C1]. apply Z.leb_le in C2. apply Z.leb_le in C3.
    destruct Hp as [Hp|[]]. injection Hp as <- <- <-. subst w.
    split; [lia|]. split; [lia|]. right. exists z. split; [reflexivity|]. split; [reflexivity|]. exact HK.
  - (* [comment removed for export] *) destruct (Z.ltb ilo (DP + DPN.TABSZ) && Z.ltb DP ihi)%bool eqn:C; [|destruct Hp].
    apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2.
    destruct Hp as [Hp|[]]. injection Hp as <- <- <-.
    split; [lia|]. split; [lia|]. left. split; [reflexivity|]. exists ilo, ihi. split; [exact HK | lia].
Qed.

Lemma tab_ok_sound : forall E M k n0,
  know_ok SEGS E M k -> DPN.tab_ok DP k n0 = true -> 0 <= n0 < 2 ^ 31 ->
  forall b, 0 <= b < 2 ^ 20 ->
  exists bs, rdn SEGS M (Z_to_bv 64 (DP + 4 * b)) 4 = Some bs /\ length bs = 4%nat /\ 0 <= bytes_le_to_Z bs <= n0.
Proof.
  intros E M k n0 HK H Hn0 b Hb. unfold DPN.tab_ok in H. apply andb_prop in H as [Hall Hreach].
  assert (LL : 0 <= DP /\ DP + DPN.TABSZ <= 2 ^ 64) by (unfold DPN.TABSZ; lia).
  destruct (reach_cover _ _ DP (DP + 4 * b) Hreach ltac:(unfold DPN.TABSZ; lia)) as (s & e & v & Hin & Hx).
  pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as Hok. cbn [DPN.piece_ok] in Hok.
  apply andb_prop in Hok as [Hok Hv]. apply andb_prop in Hok as [Hok Hse]. apply andb_prop in Hok as [Hs He].
  apply Z.eqb_eq in Hs. apply Z.eqb_eq in He. apply Z.ltb_lt in Hse.
  apply Z.mod_divide in Hs as [qs Hqs]; [|lia]. apply Z.mod_divide in He as [qe Hqe]; [|lia].
  assert (Hxe : DP + 4 * b + 4 <= e) by lia.
  destruct (tab_pieces_in k s e v Hin) as (Ds & De & ALT).
  destruct ALT as [[Hv0 HX] | HX]; [destruct HX as (lo & hi & HinK & Hlo & Hhi) | destruct HX as (z & Hvz & He4 & HinK)]; subst v.
  - (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KI. cbn [kentry_ok] in KI. destruct KI as (_ & _ & KN).
    exists (repeat (Z_to_bv 8 0) 4).
    split; [|split; [reflexivity | replace (bytes_le_to_Z (repeat (Z_to_bv 8 0) 4)) with 0 by (vm_compute; reflexivity); lia]].
    apply rdn_none_img; [lia | cbn; lia |]. intros j Hj. split.
    + apply KN. cbn in Hj. lia.
    + apply IMG0. rewrite u64_lit by (cbn in Hj; lia). cbn in Hj. unfold DPN.TABSZ in De. lia.
  - (* [comment removed for export] *)
    apply andb_prop in Hv as [Hz0 Hzn]. apply Z.leb_le in Hz0. apply Z.leb_le in Hzn.
    assert (Hsx : s = DP + 4 * b) by lia. subst s.
    pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KW. cbn [kentry_ok] in KW. destruct KW as (_ & Hfl & Hrd).
    rewrite <- (Z_to_bv_bv_unsigned 64 (adenot E _)) in Hrd. rewrite (flat_u E _ _ Hfl) in Hrd. rewrite estart_lit0 in Hrd.
    cbn [edenot] in Hrd. unfold word_to_le_bytes in Hrd. rewrite u64_lit in Hrd by lia.
    exists (Z_to_le_bytes 4 z). split; [exact Hrd|]. split; [apply length_Z_to_le_bytes|].
    rewrite bytes_le_Z_to_le by lia. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma zids_in : forall n0 id, In id (DPN.zids n0) -> 1 <= id <= n0.
Proof.
  intros n0 id H. unfold DPN.zids in H. apply in_map_iff in H as (m & <- & Hm). apply in_seq in Hm. lia.
Qed.
Lemma in_zids : forall n0 id, 0 <= n0 -> 1 <= id <= n0 -> In id (DPN.zids n0).
Proof.
  intros n0 id Hn H. unfold DPN.zids. apply in_map_iff. exists (Z.to_nat id). split; [lia|]. apply in_seq. lia.
Qed.

Theorem node_init_sound : forall args0,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => DPN.node_init SEGS DP SB IH cs args0).
Proof.
  intros args0 cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := M_of E cs model FULL) in *.
  unfold DPN.node_init, DPN.init_cells, DPN.init_tests in Hn.
  destruct (DPN.init_args args0) as [[[nc fc] k0]|]; [|discriminate].
  destruct (DPN.klit SEGS (kn cs) (ELit 0) (DP + 4194304) 4) as [n0|] eqn:Hn0; [|discriminate].
  destruct (DPN.kreadn SEGS (kn cs) (ELit 0) (DP + 4194320) 8) as [eB|] eqn:HeB; [|discriminate].
  destruct (DPN.klit SEGS (kn cs) (ELit 0) SB 8) as [tf0|] eqn:Htf; [|discriminate].
  destruct (DPN.kreadn SEGS (kn cs) (ELit 0) (SB + 16) 8) as [eP|] eqn:HeP; [|discriminate].
  destruct (DPN.klit SEGS (kn cs) (ELit 0) (SB + 24) 4) as [st0|] eqn:Hst; [|discriminate].
  destruct (xlo (kn cs) eB) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) eB) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) eP) as [plo|] eqn:Hplo; [|discriminate].
  destruct (xhi (kn cs) eP) as [phi|] eqn:Hphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hall; [|discriminate] end.
  cbn [forallb andb] in Hall.
  repeat match type of Hall with (?a && ?b)%bool = true => apply andb_prop in Hall; destruct Hall as [?X Hall]; revert X end.
  intros Hnodes Htab HwP HwB Hap Hphi64 HplIH Hbhi64 HblIH Hroom3 Hroom2 Hroom1 Hk0 Hfc Hnc. clear Hall.
  apply andb_prop in Hnc as [Hnc1 Hnc2]. apply Z.leb_le in Hnc1. apply Z.leb_le in Hnc2.
  apply andb_prop in Hfc as [Hfc1 Hfc2]. apply Z.leb_le in Hfc1. apply Z.leb_le in Hfc2.
  apply Z.leb_le in Hk0.
  apply andb_prop in Hroom1 as [Hn00 Hroom1]. apply Z.leb_le in Hn00. apply Z.ltb_lt in Hroom1.
  apply andb_prop in Hroom2 as [Htf00 Hroom2]. apply Z.leb_le in Htf00. apply Z.leb_le in Hroom2.
  apply andb_prop in Hroom3 as [Hst00 Hroom3]. apply Z.leb_le in Hst00. apply Z.ltb_lt in Hroom3.
  apply Z.leb_le in HblIH. apply Z.ltb_lt in Hbhi64. apply Z.leb_le in HplIH. apply Z.ltb_lt in Hphi64. unfold two64 in Hbhi64, Hphi64.
  injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Bblo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Bbhi.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hplo) as Bplo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hphi) as Bphi.
  set (B := bv_unsigned (edenot E eB)) in *. set (P := bv_unsigned (edenot E eP)) in *.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) eB 0 (16 * nc) HKN HKN HwB ltac:(lia)) as (SB_ & SB0 & SB64).
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) eP 0 (8 * fc) HKN HKN HwP ltac:(lia)) as (SP_ & SP0 & SP64).
  unfold estart in SB_, SB0, SB64, SP_, SP0, SP64. cbn [a_base a_off] in SB_, SB0, SB64, SP_, SP0, SP64.
  fold B in SB_, SB0, SB64. fold P in SP_, SP0, SP64. rewrite Z.add_0_r in SB_, SB0, SB64, SP_, SP0, SP64.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) _ _ _ _ _ _ HKN Hap) as DBP.
  unfold estart in DBP. cbn [a_base a_off] in DBP. rewrite !elenZ_lit in DBP by lia. fold B in DBP. fold P in DBP.
  assert (FL : forall b o n, 0 <= bv_unsigned (edenot E b) + o -> 0 <= n -> bv_unsigned (edenot E b) + o + n <= 2 ^ 64 -> 0 < n ->
               flat E (SA b o) n).
  { intros b o n H1 H2 H3 H4. unfold flat, estart. cbn [a_base a_off]. lia. }
  assert (E0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; apply u64_lit; lia).
  (* [comment removed for export] *)
  pose proof (klit_cell E M (kn cs) (ELit 0) (DP + 4194304) 4 n0 HKN Hn0 ltac:(lia) ltac:(lia) ltac:(apply FL; rewrite ?E0; lia) ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)) as Cn.
  pose proof (klit_cell E M (kn cs) (ELit 0) SB 8 tf0 HKN Htf ltac:(lia) ltac:(lia) ltac:(apply FL; rewrite ?E0; lia) ltac:(change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia)) as Ctf.
  pose proof (klit_cell E M (kn cs) (ELit 0) (SB + 24) 4 st0 HKN Hst ltac:(lia) ltac:(lia) ltac:(apply FL; rewrite ?E0; lia) ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)) as Cst.
  rewrite estart_lit0 in Cn, Ctf, Cst.
  destruct (kreadn_rdn E M (kn cs) (ELit 0) (DP + 4194320) 8 eB HKN HeB ltac:(lia) ltac:(lia) ltac:(apply FL; rewrite ?E0; lia)) as (bsB & RB1 & RB2 & RB3).
  destruct (kreadn_rdn E M (kn cs) (ELit 0) (SB + 16) 8 eP HKN HeP ltac:(lia) ltac:(lia) ltac:(apply FL; rewrite ?E0; lia)) as (bsP & RP1 & RP2 & RP3).
  rewrite estart_lit0 in RB1, RP1.
  assert (W8 : forall bs (w : word), length bs = 8%nat -> Z_to_bv 64 (bytes_le_to_Z bs) = w -> bs = word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned w))).
  { intros bs w Hl Hw. pose proof (bytes_le_to_Z_bound bs) as Hbd. rewrite Hl in Hbd. change (8 * Z.of_nat 8) with 64 in Hbd.
    apply (f_equal bv_unsigned) in Hw. rewrite u64_lit in Hw by lia.
    unfold word_to_le_bytes. rewrite Z_to_bv_bv_unsigned. rewrite <- Hw, <- Hl. symmetry. apply Z_to_le_bytes_lez. }
  assert (CB : cellG SEGS M 8 (DP + 4194320) B).
  { split; [| unfold B; apply u64_range]. rewrite RB1. f_equal. apply W8; [exact RB2 | exact RB3]. }
  assert (CP : cellG SEGS M 8 (SB + 16) P).
  { split; [| unfold P; apply u64_range]. rewrite RP1. f_equal. apply W8; [exact RP2 | exact RP3]. }
  (* [comment removed for export] *)
  pose proof (tab_ok_sound E M (kn cs) n0 HKN Htab ltac:(lia)) as TAB.
  assert (NODES : forall id, 1 <= id <= n0 ->
            exists l hv, DPN.klit SEGS (kn cs) eB (16 * id + 8) 4 = Some l /\ 0 <= l < id
                      /\ DPN.kreadn SEGS (kn cs) eB (16 * id) 8 = Some hv).
  { intros id Hid. pose proof (proj1 (forallb_forall _ _) Hnodes id (in_zids n0 id ltac:(lia) Hid)) as Hx.
    unfold DPN.node_okb in Hx.
    destruct (DPN.klit SEGS (kn cs) eB (16 * id + 8) 4) as [l|]; [|discriminate].
    destruct (DPN.kreadn SEGS (kn cs) eB (16 * id) 8) as [hv|]; [|discriminate].
    apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists l, hv. repeat split; try lia; reflexivity. }
  (* [comment removed for export] *)
  set (dtab := fun b : Z => match rdn SEGS M (Z_to_bv 64 (DP + 4 * b)) 4 with Some bs => bytes_le_to_Z bs | None => 0 end).
  set (dlnk := fun id : Z => match DPN.klit SEGS (kn cs) eB (16 * id + 8) 4 with Some l => l | None => 0 end).
  set (dhsh := fun id : Z => match DPN.kreadn SEGS (kn cs) eB (16 * id) 8 with Some v => edenot E v | None => Z_to_bv 64 0 end).
  assert (INV : depot_invG SEGS DP SB IH B P nc fc k0 M).
  { exists (DepotInvG.DS n0 tf0 st0 dtab dlnk dhsh).
    cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st DepotInvG.d_tab DepotInvG.d_lnk DepotInvG.d_hsh].
    split; [|split; [unfold depot_geomG; repeat split; lia | split; [lia | split; [lia | split; [lia | split; [lia | split; (apply okr_of_store_ok; [lia | lia | lia | assumption])]]]]]].
    unfold depot_cellsG. cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st DepotInvG.d_tab DepotInvG.d_lnk DepotInvG.d_hsh].
    split; [|split; [exact Cn | split; [exact CB | split; [| split; [exact Ctf | split; [exact CP | split; [exact Cst | lia]]]]]]].
    - (* [comment removed for export] *) intros b Hb. destruct (TAB b Hb) as (bs & R1 & R2 & R3).
      assert (Hv : dtab b = bytes_le_to_Z bs) by (unfold dtab; rewrite R1; reflexivity). rewrite Hv.
      pose proof (bytes_le_to_Z_bound bs) as Hbd. rewrite R2 in Hbd. change (8 * Z.of_nat 4) with 32 in Hbd.
      split; [|lia]. split; [| change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia].
      rewrite R1. f_equal. unfold word_to_le_bytes. rewrite u64_lit by lia. rewrite <- R2. symmetry. apply Z_to_le_bytes_lez.
    - (* [comment removed for export] *) intros id Hid. destruct (NODES id Hid) as (l & hv & Hl & Hlid & Hhv).
      assert (Hdl : dlnk id = l) by (unfold dlnk; rewrite Hl; reflexivity).
      assert (Hdh : dhsh id = edenot E hv) by (unfold dhsh; rewrite Hhv; reflexivity).
      rewrite Hdl, Hdh.
      assert (FLh : flat E (SA eB (16 * id)) (Z.of_nat 8)) by (apply FL; cbn; lia).
      assert (FLl : flat E (SA eB (16 * id + 8)) (Z.of_nat 4)) by (apply FL; cbn; lia).
      destruct (kreadn_rdn E M (kn cs) eB (16 * id) 8 hv HKN Hhv ltac:(lia) ltac:(lia) FLh) as (bsh & H1 & H2 & H3).
      unfold estart in H1. cbn [a_base a_off] in H1. fold B in H1.
      split; [rewrite H1; f_equal; rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E hv)); apply W8; [exact H2 | exact H3]|].
      split; [|lia].
      pose proof (klit_cell E M (kn cs) eB (16 * id + 8) 4 l HKN Hl ltac:(lia) ltac:(lia) FLl ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)) as Cl.
      unfold estart in Cl. cbn [a_base a_off] in Cl. fold B in Cl. replace (B + (16 * id + 8)) with (B + 16 * id + 8) in Cl by lia. exact Cl. }
  (* [comment removed for export] *)
  assert (HT : know_ok SEGS E M [KPriv 0 (DPN.init_rs DP SB eB eP nc fc) [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH] k0]).
  { constructor; [|constructor]. cbn [kentry_ok]. split.
    - unfold DPN.init_rs.
      assert (FL' : forall b o z, 0 <= z < 2 ^ 64 -> flat E (SA b o) z -> flat E (SA b o) (elenZ E (ELit z)))
        by (intros b o z Hz Hf; rewrite elenZ_lit by lia; exact Hf).
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (apply FL'; [lia|]); apply FL; fold B; fold P; rewrite ?E0; lia.
    - cbn [PRIV DPN.init_rs fst snd]. unfold pstart. cbn [a_base a_off]. rewrite !pvE_lit by lia.
      fold B. fold P. change (pvE E eB) with B. change (pvE E eP) with P.
      repeat (split; [lia|]). exact INV. }
  specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
  unfold add_kn in Hk. rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
  apply cs_ok_set_kn; [exact HC|].
  apply Forall_app. split; [exact HT | exact HKN].
Qed.
End Sound.

Section Table.
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
Hypothesis SEGS_wr : segs_wr_ok SEGS.
Variables DP SB IH : Z.
Hypothesis LAYOUT : 2 ^ 16 <= DP /\ DP + 4194328 <= IH /\ 2 ^ 16 <= SB /\ SB + 28 <= IH /\ IH < 2 ^ 32 /\ (DP + 4194328 <= SB \/ SB + 28 <= DP).
(* [comment removed for export] *)
Hypothesis IMG0 : forall x : word, DP <= bv_unsigned x < DP + 4194304 -> seg_rom SEGS x = Some (Z_to_bv 8 0).
Hypothesis PSPEC : put_specG SEGS DP SB IH.

Theorem dpn_xn_sound : ext_stmt SEGS A nx0 LIMIT (DPN.xn SEGS nx0 DP SB IH) SINV argH FS0.
Proof.
  intros id args. unfold DPN.xn.
  destruct (Nat.eqb id 113); [apply node_put_sound; assumption|].
  destruct (Nat.eqb id 114); [apply node_init_sound; assumption|].
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Table.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
