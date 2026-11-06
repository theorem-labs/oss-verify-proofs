(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout ATacA ASec LJ F_sec_A.
Import ListNotations.
Open Scope Z_scope.

Lemma nearest_below_spec : forall l acc p, 0 <= acc <= p -> Forall (fun x => 0 <= x) l ->
  let r := nearest_below acc l p in (r = acc \/ In r l) /\ acc <= r <= p /\ Forall (fun x => x <= p -> x <= r) l.
Proof.
  induction l as [|x l IH]; intros acc p Hacc Hpos; cbn.
  - repeat split; try lia. constructor.
  - apply Forall_cons_iff in Hpos as [Hx Hpos].
    set (acc' := if (x <=? p) && (p - x <? p - acc) then x else acc).
    assert (A' : 0 <= acc' <= p /\ acc <= acc' /\ (x <= p -> x <= acc') /\ (acc' = acc \/ acc' = x)).
    { subst acc'. destruct (Z.leb_spec x p); destruct (Z.ltb_spec (p - x) (p - acc)); cbn; lia. }
    destruct (IH acc' p ltac:(lia) Hpos) as (R1 & R2 & R3).
    repeat split; try lia.
    + destruct R1 as [R1|R1]; [| right; right; exact R1]. destruct A' as (_ & _ & _ & [E|E]); [left; congruence| right; left; congruence].
    + constructor; [intros; lia|]. exact R3.
Qed.

Lemma sec_find_some : forall l p c, sec_find l p = Some c -> In c l /\ sc_beg c <= p < sc_beg c + sc_msize c.
Proof.
  induction l as [|d l IH]; intros p c H; cbn in H; [discriminate|].
  destruct (Z.leb_spec (sc_beg d) p); destruct (Z.ltb_spec p (sc_beg d + sc_msize d)); cbn in H.
  1: { inversion H; subst. split; [left; reflexivity| lia]. }
  all: destruct (IH p c H) as [A B]; split; [right; exact A| exact B].
Qed.

Lemma sec_find_none : forall l p, sec_find l p = None -> forall c, In c l -> p < sc_beg c \/ sc_beg c + sc_msize c <= p.
Proof.
  induction l as [|d l IH]; intros p H c Hc; [destruct Hc|]. cbn in H.
  destruct (Z.leb_spec (sc_beg d) p); destruct (Z.ltb_spec p (sc_beg d + sc_msize d)); cbn in H; try discriminate;
    destruct Hc as [<-|Hc]; try lia; apply (IH p H c Hc).
Qed.

Lemma chunks_sep_In2 : forall l, chunks_sep l -> forall c d, In c l -> In d l -> c = d \/ apart_chunks c d \/ apart_chunks d c.
Proof.
  induction 1 as [|c0 l Hf Hs IH]; intros c d Hc Hd; [destruct Hc|].
  destruct Hc as [<-|Hc], Hd as [<-|Hd].
  - left; reflexivity.
  - right; left. exact (proj1 (Forall_forall _ _) Hf d Hd).
  - right; right. exact (proj1 (Forall_forall _ _) Hf c Hc).
  - apply IH; assumption.
Qed.

Section M.
Context {HC : HasCeiling}.
Variable AL : alayout.

#[using="Type"] Lemma nearest_chunk : forall S p, sec_wf AL S -> 0 <= p ->
  let r := nearest_below 0 (map sc_beg (se_chunks S)) p in
  match sec_find (se_chunks S) p with
  | Some c => In c (se_chunks S) /\ r = sc_beg c /\ sc_beg c <= p < sc_beg c + sc_msize c
  | None => r = 0 \/ exists d, In d (se_chunks S) /\ r = sc_beg d /\ sc_beg d + sc_msize d <= p
  end.
Proof.
  intros S p WF P0. destruct WF as (_ & _ & _ & _ & _ & CK & SEP).
  assert (POS : Forall (fun x => 0 <= x) (map sc_beg (se_chunks S))).
  { apply Forall_map. eapply Forall_impl; [| exact CK]. intros c [_ [A _]]. cbn. lia. }
  destruct (nearest_below_spec (map sc_beg (se_chunks S)) 0 p ltac:(lia) POS) as (R1 & R2 & R3).
  set (r := nearest_below 0 (map sc_beg (se_chunks S)) p) in *. cbv zeta.
  destruct (sec_find (se_chunks S) p) as [c|] eqn:FD.
  - destruct (sec_find_some _ _ _ FD) as [Hin Hrange]. split; [exact Hin|]. split; [| exact Hrange].
    pose proof (proj1 (Forall_forall _ _) R3 (sc_beg c) (in_map _ _ _ Hin) ltac:(lia)) as LE.
    destruct R1 as [R1|R1].
    + exfalso. pose proof (proj1 (Forall_forall _ _) CK c Hin) as [_ [A _]]. lia.
    + apply in_map_iff in R1 as (d & Hd & Hind).
      destruct (chunks_sep_In2 _ SEP c d Hin Hind) as [E|[AP|AP]]; [subst d; symmetry; exact Hd| |];
        unfold apart_chunks in AP; pose proof (proj1 (Forall_forall _ _) CK d Hind) as (_ & _ & SZ & MS & _);
        assert (0 < sc_msize d) by (rewrite MS; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia);
        pose proof (proj1 (Forall_forall _ _) R3 (sc_beg d) (in_map _ _ _ Hind)); lia.
  - destruct R1 as [R1|R1]; [left; exact R1| right].
    apply in_map_iff in R1 as (d & Hd & Hind). exists d. split; [exact Hind|]. split; [symmetry; exact Hd|].
    destruct (sec_find_none _ _ FD d Hind); lia.
Qed.
End M.

Lemma skipn_firstn_cons {X} : forall (l : list X) i n x,
  nth_error l i = Some x -> (i < n)%nat -> skipn i (firstn n l) = x :: skipn (S i) (firstn n l).
Proof.
  intros l i n x Hn Hi. revert l n Hn Hi. induction i as [|i IH]; intros [|y l] [|n] Hn Hi; cbn in *; try discriminate; try lia.
  - inversion Hn; subst; reflexivity.
  - cbn. apply IH; [exact Hn| lia].
Qed.

Section GB.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation L := (al_thread AL).
Notation PARR := (al_parr AL).

Definition gbb_entry : Z := 0x35b1c.

Definition gbb_step (acc ch p : Z) : Z := if (ch <=? p) && (p - ch <? p - acc) then ch else acc.

#[using="Type"] Lemma gbb_body : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 aw a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ws : list word) (i : nat) (w : word) (p acc e : Z),
  mem_inv asegs m -> u64arr asegs m PARR ws -> nth_error ws i = Some w -> bv_unsigned aw = acc -> 0 <= acc <= p -> p < 2^64 -> 0 <= PARR ->
  evt asegs (fun ms' => exists x5' aw' a5' a6' a7',
      ms' = MS (mkR ra sp gp tp x5' x6 x7 s0 s1 a0 (wz p) (wz (PARR + 8 * Z.of_nat i)) aw' (wz e) a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35b80) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m /\ bv_unsigned aw' = gbb_step acc (bv_unsigned w) p)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 (wz p) (wz (PARR + 8 * Z.of_nat i)) aw (wz e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x35b88) fc None m (seg_rom asegs)).
Proof.
  intros until e. intros MI PARRu NTH AW ACC P64 PA0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
  pose proof (u64arr_read asegs _ PARR ws (Z.of_nat i) w (wa (PARR + 8 * Z.of_nat i)) PARRu ltac:(rewrite Nat2Z.id; exact NTH) ltac:(lia) eq_refl) as RD.
  pose proof (bv_unsigned_in_range _ w) as WR. change (bv_modulus 64) with 18446744073709551616 in WR.
  zstep.
  do 3 zstep.   rewrite AW.
  zstep. if_cases K1; zify_cond K1.
  -
    zstep. if_cases K2; zify_cond K2.
    +   finish. rewrite AW. unfold gbb_step. destruct (Z.leb_spec (bv_unsigned w) p); [lia| reflexivity].
    + zstep. zstep.   finish.
      unfold gbb_step. rewrite (Z.mod_small (p - bv_unsigned w)) in K1 by lia.
      destruct (Z.leb_spec (bv_unsigned w) p); [| lia]. destruct (Z.ltb_spec (p - bv_unsigned w) (p - acc)); [reflexivity| lia].
  - zstep.   zstep. if_cases K2; zify_cond K2.
    + finish. rewrite AW. unfold gbb_step. destruct (Z.leb_spec (bv_unsigned w) p); [lia| reflexivity].
    + zstep. zstep. zstep.   finish.
      rewrite AW. unfold gbb_step. rewrite (Z.mod_small (p - bv_unsigned w)) in K1 by lia.
      destruct (Z.leb_spec (bv_unsigned w) p); [| reflexivity]. destruct (Z.ltb_spec (p - bv_unsigned w) (p - acc)); [lia| reflexivity].
Qed.

#[using="Type"] Lemma gbb_loop : forall (k i : nat) (ra sp gp tp x5 x6 x7 s0 s1 a0 aw a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ws : list word) (n : nat) (p acc : Z),
  mem_inv asegs m -> u64arr asegs m PARR ws -> (i + S k = n)%nat -> (n <= length ws)%nat -> bv_unsigned aw = acc ->
  0 <= acc <= p -> p < 2^64 -> 0 <= PARR -> PARR + 8 * Z.of_nat n < 2^64 ->
  evt asegs (fun ms' => exists x5' aw' a5' a6' a7',
      ms' = MS (mkR ra sp gp tp x5' x6 x7 s0 s1 a0 (wz p) (wz (PARR + 8 * Z.of_nat n)) aw' (wz (PARR + 8 * Z.of_nat n)) a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35bb4) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m
      /\ bv_unsigned aw' = nearest_below acc (map bv_unsigned (skipn i (firstn n ws))) p)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 (wz p) (wz (PARR + 8 * Z.of_nat i)) aw (wz (PARR + 8 * Z.of_nat n)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x35b88) fc None m (seg_rom asegs)).
Proof.
  intros k; induction k as [|k IH]; intros until acc; intros MI PARRu IK NLE AW ACC P64 PA0 PE64.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
  all: destruct (nth_error ws i) as [w|] eqn:NTH; [| exfalso; apply nth_error_None in NTH; lia].
  all: call (gbb_body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ws i w p acc (PARR + 8 * Z.of_nat n) MI PARRu NTH AW ACC P64 PA0).
  all: lazymatch goal with Hs : bv_unsigned _ = gbb_step _ _ _ |- _ => rename Hs into AW2 end.
  all: pose proof (nearest_below_spec [bv_unsigned w] acc p ACC ltac:(constructor; [pose proof (bv_unsigned_in_range _ w); lia| constructor])) as NB;
       cbn [nearest_below] in NB; unfold gbb_step in AW2; rewrite <- AW2 in NB.
  all: zstep.
  all: rewrite (skipn_firstn_cons ws i n w NTH) by lia; cbn [map nearest_below].
  - zstep. replace (PARR + 8 * Z.of_nat i + 8) with (PARR + 8 * Z.of_nat n) by lia. if_true_z.
    finish. rewrite skipn_all2 by (rewrite length_firstn; lia). cbn. exact AW2.
  - zstep. if_false_z.
    replace (PARR + 8 * Z.of_nat i + 8) with (PARR + 8 * Z.of_nat (S i)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (IH (S i) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm ws n p _ MIx PARRu ltac:(lia) NLE AW2 ltac:(lia) P64 PA0 PE64) end end.
    finish.
Qed.

Definition gbb_post (ra : word) (q : Z) (gp tp x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (S : asec) (p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x5 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz (sec_block_begin S p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 32, q); (SEC_MTX, SEC_MTX + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ RSEC AL S m'.

#[using="Type"] Lemma gbb_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q lo p : Z) (S : asec),
  mem_inv asegs m -> alayout_ok AL -> RSEC AL S m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q <= 2^47 ->
  a0 = wz SEC -> a1 = wz p -> 0 <= p < 2^64 ->
  evt asegs (gbb_post ra q gp tp x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc lo S p m)
    (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz gbb_entry) fc None m (seg_rom asegs)).
Proof.
  intros until S. intros MI AO RS ST CLO LOQ QHI -> -> PR64. unfold gbb_entry.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct RS as (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD).
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS).
  pose proof WF as (W0 & _ & W2 & W3 & W4 & W5 & W6).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & P3 & P4 & P5 & P6 & P7). clear P3 P6 P7.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(q - 32, q); (SEC_MTX, SEC_MTX + 4)] mm) as MU; pose proof (wmono_refl asegs mm) as WM end.
  carve_frame 32%nat ST.
  do 5 zstep.
  do 4 zstep.
  unfold b8 in MTX.
  amo_step.   try fold_cb_load.
  do 4 zstep.
  amo_step.
  zstep. if_false.
  zstep.
  zstep. if_false.
  zstep.
  assert (WN : 0 <= se_n S) by (unfold se_n; lia).
  zstep. if_cases KN; zify_cond KN.
  -
    zstep.
    zstep.
    lazymatch type of MTX with rw_cells _ ?mm _ _ =>
      assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
        by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
            lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
            cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
      clear MTX end.
    sstep.
    do 4 zstep.
    zstep. replace (q + -32 + 32) with q by lia. zstep.
    release_frame FR ST q.
    unfold gbb_post. replace (sec_block_begin S p) with 0 by (unfold sec_block_begin; destruct (se_chunks S) eqn:EC; [reflexivity| unfold se_n in KN; rewrite EC in KN; cbn in KN; lia]).
    finish.

    unfold RSEC. split; [exact WF|]. split; [split; [exact ENV| split; assumption]|]. split; [| split; [exists ws; split; [exact PARRu| split; [exact LWS| exact FWS]]|]].
    + unfold sec_vars. split; [exists j24, j32, j40, jsb, jpad, na, nf, cur, mx; exact VC|]. split; [exists bsl; split; [exact BSL| exact LBSL]|].
      split; [| exists g16, g24; exact GST].
      lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
        destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
        lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
        cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
    + eapply (hdrs_rep_gframe S _ m _ HD (gmunch_of_munch _ _ _ MU) WM).
      apply Forall_forall; intros c Hc.
      pose proof (proj1 (Forall_forall _ _) W5 c Hc) as CK; unfold chunk_ok in CK; destruct CK as (_ & CK2 & CK3 & CK4 & _ & CK6 & _).
      assert (CM : 32 <= sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
      clear - CK2 CK6 CM CLO LOQ; cbn [disjoint_from]; repeat split; lia.
  -
    zstep.   zstep.
    do 2 zstep.
    rewrite (Z.shiftl_mul_pow2 (se_n S) 3) by lia. change (2 ^ 3) with 8.
    set (n := length (se_chunks S)).
    replace (PARR + se_n S * 8) with (PARR + 8 * Z.of_nat n) by (unfold se_n; lia).
    replace (Z_to_bv 64 PARR) with (Z_to_bv 64 (PARR + 8 * Z.of_nat 0)) by (f_equal; lia).
    zstep.
    assert (NPOS : (0 < n)%nat) by (unfold se_n in KN; lia).
    assert (NLE : (n <= length ws)%nat) by (unfold se_n in W3; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with MIx : mem_inv asegs mm |- _ =>
      call (gbb_loop (n - 1) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm ws n p 0 MIx PARRu ltac:(lia) NLE
              ltac:(apply unsigned_lit; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold se_n in W3; lia)) end end.
    match goal with Hr : bv_unsigned ?awr = nearest_below 0 _ p |- _ => rename Hr into AWR; rename awr into aw end.
    assert (FM : map bv_unsigned (firstn n ws) = map sc_beg (se_chunks S)).
    { subst n. rewrite FWS, map_map. apply map_ext_in. intros c Hc.
      pose proof (proj1 (Forall_forall _ _) W5 c Hc) as (_ & CK2 & CK3 & CK4 & _ & CK6 & _).
      assert (0 < sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
      apply unsigned_lit. lia. }
    rewrite skipn_O in AWR. rewrite FM in AWR. clear FM.
    destruct (sec_find (se_chunks S) p) as [c|] eqn:FD.
    +
      pose proof (nearest_chunk AL S p WF ltac:(lia)) as NC. rewrite FD in NC. cbv zeta in NC. destruct NC as (Hc & RC & PC).
      rewrite RC in AWR.
      pose proof (proj1 (Forall_forall _ _) W5 c Hc) as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & _).
      assert (CM : 4096 <= sc_msize c) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
      assert (EA : aw = wz (sc_beg c)) by (rewrite <- (Z_to_bv_bv_unsigned aw); rewrite AWR; reflexivity).
      rewrite EA. clear EA AWR aw.
      zstep. if_false_z.
      destruct (In_nth_error _ _ Hc) as [ic Hic].
      pose proof (HD ic c Hic) as HDR. unfold hdr_cells in HDR.
      lazymatch type of MU with munch ?W _ ?mm => apply (rw_cells_transport asegs W m mm) in HDR; [| exact MU| exact WM| clear - CK2 CK6 CM CLO LOQ; cbn; repeat split; lia] end.
      zstep.
      zstep. if_false_z.
      do 2 zstep.
      zstep. if_false_z.
      zstep. if_false_z.
      zstep. if_false_z.
      zstep.
      do 2 zstep.
      replace (Z.land 4095 (sc_beg c)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; clear - CK1; lia).
      zstep. if_false_z.
      do 2 zstep.
      zstep.
      lazymatch type of MTX with rw_cells _ ?mm _ _ =>
        assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
          by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
              lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
              cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
        clear MTX end.
      sstep.
      do 4 zstep.
      zstep. replace (q + -32 + 32) with q by lia. zstep.
      release_frame FR ST q.
      unfold gbb_post. replace (sec_block_begin S p) with (sc_beg c + 4096) by (unfold sec_block_begin; rewrite FD; reflexivity).
      replace (4096 + sc_beg c) with (sc_beg c + 4096) by lia.
      finish.
      unfold RSEC. split; [exact WF|]. split; [split; [exact ENV| split; assumption]|]. split; [| split; [exists ws; split; [exact PARRu| split; [exact LWS| exact FWS]]|]].
      * unfold sec_vars. split; [exists j24, j32, j40, jsb, jpad, na, nf, cur, mx; exact VC|]. split; [exists bsl; split; [exact BSL| exact LBSL]|].
        split; [| exists g16, g24; exact GST].
        lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
          destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
          lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
          cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
      * eapply (hdrs_rep_gframe S _ m _ HD (gmunch_of_munch _ _ _ MU) WM).
        apply Forall_forall; intros c' Hc'.
        pose proof (proj1 (Forall_forall _ _) W5 c' Hc') as CK; unfold chunk_ok in CK; destruct CK as (_ & CK2' & CK3' & CK4' & _ & CK6' & _).
        assert (CM' : 32 <= sc_msize c') by (rewrite CK4'; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
        clear - CK2' CK6' CM' CLO LOQ; cbn [disjoint_from]; repeat split; lia.
    +
      pose proof (nearest_chunk AL S p WF ltac:(lia)) as NC. rewrite FD in NC. cbv zeta in NC.
      zstep. if_cases K0; zify_cond K0.
      *
        zstep.
        zstep.
        lazymatch type of MTX with rw_cells _ ?mm _ _ =>
          assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
            by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
                lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
                cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
          clear MTX end.
        sstep.
        do 4 zstep.
        zstep. replace (q + -32 + 32) with q by lia. zstep.
        release_frame FR ST q.
        unfold gbb_post. replace (sec_block_begin S p) with 0 by (unfold sec_block_begin; rewrite FD; reflexivity).
        finish.
        unfold RSEC. split; [exact WF|]. split; [split; [exact ENV| split; assumption]|]. split; [| split; [exists ws; split; [exact PARRu| split; [exact LWS| exact FWS]]|]].
        -- unfold sec_vars. split; [exists j24, j32, j40, jsb, jpad, na, nf, cur, mx; exact VC|]. split; [exists bsl; split; [exact BSL| exact LBSL]|].
           split; [| exists g16, g24; exact GST].
           lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
             destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
             lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
             cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
        -- eapply (hdrs_rep_gframe S _ m _ HD (gmunch_of_munch _ _ _ MU) WM).
           apply Forall_forall; intros c' Hc'.
           pose proof (proj1 (Forall_forall _ _) W5 c' Hc') as CK; unfold chunk_ok in CK; destruct CK as (_ & CK2' & CK3' & CK4' & _ & CK6' & _).
           assert (CM' : 32 <= sc_msize c') by (rewrite CK4'; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
           clear - CK2' CK6' CM' CLO LOQ; cbn [disjoint_from]; repeat split; lia.
      *
        destruct NC as [R0|(d & Hd & Rd & Pd)]; [exfalso; lia|].
        rewrite Rd in AWR.
        pose proof (proj1 (Forall_forall _ _) W5 d Hd) as (CK1 & CK2 & CK3 & CK4 & CK5 & CK6 & _).
        assert (CM : 4096 <= sc_msize d) by (rewrite CK4; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
        assert (EA : aw = wz (sc_beg d)) by (rewrite <- (Z_to_bv_bv_unsigned aw); rewrite AWR; reflexivity).
        rewrite EA. clear EA AWR K0 aw.
        destruct (In_nth_error _ _ Hd) as [ic Hic].
        pose proof (HD ic d Hic) as HDR. unfold hdr_cells in HDR.
        lazymatch type of MU with munch ?W _ ?mm => apply (rw_cells_transport asegs W m mm) in HDR; [| exact MU| exact WM| clear - CK2 CK6 CM CLO LOQ; cbn; repeat split; lia] end.
        zstep.
        zstep. if_false_z.
        do 2 zstep.
        zstep. if_false_z.
        zstep. if_false_z.
        zstep. if_true_z.
        zstep.
        zstep.
        lazymatch type of MTX with rw_cells _ ?mm _ _ =>
          assert (MTX' : rw_cells asegs mm SEC_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]])
            by (destruct MTX as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
                lazymatch goal with |- bytes_at _ _ _ ?l => replace l with (cells_bytes [C4 (Z_to_bv 64 1)]); [exact Hb|] end;
                cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]);
          clear MTX end.
        sstep.
        do 4 zstep.
        zstep. replace (q + -32 + 32) with q by lia. zstep.
        release_frame FR ST q.
        unfold gbb_post. replace (sec_block_begin S p) with 0 by (unfold sec_block_begin; rewrite FD; reflexivity).
        finish.
        unfold RSEC. split; [exact WF|]. split; [split; [exact ENV| split; assumption]|]. split; [| split; [exists ws; split; [exact PARRu| split; [exact LWS| exact FWS]]|]].
        -- unfold sec_vars. split; [exists j24, j32, j40, jsb, jpad, na, nf, cur, mx; exact VC|]. split; [exists bsl; split; [exact BSL| exact LBSL]|].
           split; [| exists g16, g24; exact GST].
           lazymatch goal with M : rw_cells asegs _ 725376 _ |- _ =>
             destruct M as [[Hwf Hb] Hw]; split; [split; [cbn; ctauto| ]| exact Hw];
             lazymatch type of Hb with bytes_at _ _ _ ?l => replace (cells_bytes _) with l; [exact Hb|] end;
             cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ] end.
        -- eapply (hdrs_rep_gframe S _ m _ HD (gmunch_of_munch _ _ _ MU) WM).
           apply Forall_forall; intros c' Hc'.
           pose proof (proj1 (Forall_forall _ _) W5 c' Hc') as CK; unfold chunk_ok in CK; destruct CK as (_ & CK2' & CK3' & CK4' & _ & CK6' & _).
           assert (CM' : 32 <= sc_msize c') by (rewrite CK4'; unfold sec_msize, rup4k; Z.div_mod_to_equations; nia).
           clear - CK2' CK6' CM' CLO LOQ; cbn [disjoint_from]; repeat split; lia.
Qed.
End GB.
