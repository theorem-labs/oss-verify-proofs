(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast Cells Arr RzCPS.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env.
Import ListNotations.
Open Scope Z_scope.

Ltac cut2f PC r1 r2 P :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 : word,
                 ms' = MS (@bvmap_set 5 word r1 u1 (@bvmap_set 5 word r2 u2 R)) F (Z_to_bv 64 PC) fc rv m ro /\ P u1 u2));
      [ | let u1 := fresh "u" in let u2 := fresh "u" in let E := fresh "E" in let HP := fresh "HP" in
          let ms := fresh "ms" in intros ms (u1 & u2 & E & HP); subst ms; norm_regset ]
  end.
(* [comment removed for export] *)
Ltac cut2f_done tac := apply evt_done; do 2 eexists; split; [ norm_regset; reflexivity | tac ].

Lemma shk_zero : forall (m : mem) a n X b, acc asegs m a n -> shk m b X -> 0 <= X ->
  a <= 8 * (X / 8) -> 8 * (X / 8) + 8 <= a + n -> bv_unsigned b = 0.
Proof.
  intros m a n X b H K H0 H1 H2.
  destruct (acc_read1 m a n (8 * (X / 8) + 7) H ltac:(lia)) as (b' & R & OK).
  assert (E : shad (8 * (X / 8) + 7) = shad X) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite E in R. rewrite (shk_read m b X K) in R. injection R as <-.
  destruct OK as [OK|[OK1 OK2]]; [exact OK|]. exfalso. revert OK2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Ltac shbr0 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then _ else _) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          let Z0 := fresh "Z0" in
          first [ match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (Z0 : bv_unsigned b = 0) by (apply (shk_zero m a n X b ACC K); [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ])
                  end
                | fail 1 "shbr0: no acc fact covers the granule of" X ];
          rewrite ?(sxb_small b) by lia;
          first [ brF | brT ]; clear K Z0
      end
  end.

Lemma bytes_at_read1 : forall (m : mem) A bs (i : Z), bytes_at asegs m A bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, ov_read_bytes asegs m (wa (A + i)) 1 = Some [b].
Proof.
  intros m A bs i Hb Hi.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E.
  - exists b. exact (Arr.u8ro_read asegs m A bs i b _ Hb E ltac:(lia) eq_refl).
  - apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_recell : forall (m : mem) A cs cs', rw_cells asegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] W' E1 E2. split; [split; [exact W'| rewrite E1; exact Hb]| rewrite E2; exact Hw].
Qed.



(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.
Ltac sx32_fix := repeat match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end.

(* [comment removed for export] *)
Ltac arr_sb A idx E :=
  lazymatch goal with
  | UA : u8arr asegs ?mm A ?bs, UAL : Z.of_nat (length ?bs) = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok asegs mm A bs idx (wa E) UA ltac:(lia) ltac:(f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z) end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm (Z_to_bv 64 ?E') [?b]) _) =>
      let N := fresh "UA" in
      assert (N : u8arr asegs (write_to_mem mm (wa E') [b]) A (upd bs (Z.to_nat idx) b))
        by (replace E' with (A + idx) by lia; apply (u8arr_write asegs mm A bs idx b UA); lia);
      clear UA; store_done; rename N into UA;
      rewrite <- (upd_length bs (Z.to_nat idx) b) in UAL;
      let bs' := fresh "abs" in set (bs' := upd bs (Z.to_nat idx) b) in *; clearbody bs'; try clear bs
    end
  end.

(* [comment removed for export] *)
Section KitC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma new_chunk_apart : forall Σ' (m : mem) p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m p n live0 frs usp a HA LV FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    assert (Hin' : In (p', n') ([] ++ live0)) by exact Hin.
    pose proof (af_live_disj RT AF Σ' m p n p' n' [] live0 HA LV Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.
End KitC.

(* [comment removed for export] *)
Ltac chunk_facts RT AF GP p n :=
  match goal with
  | A : ART RT ?S ?mm |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      let R1 := fresh "CKR" in let R2 := fresh "CKS" in let R3 := fresh "CKH" in
      pose proof (af_live_range RT AF S mm p n A IN) as (_ & R1 & R2);
      pose proof (gp_live_hi RT GP S mm p n A IN) as R3;
      unfold STACK_WIN, SEGTOP_A in R1, R2;
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in R1 end
  end.

(* [comment removed for export] *)
Ltac live_add_tac :=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
  repeat first [ exact He | right ].

(* [comment removed for export] *)
Lemma client_static_lo : forall a, client_static a -> 0x10000 <= a.
Proof.
  intros a ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Ltac subfp_tac := clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; tauto.

(* [comment removed for export] *)
Ltac out_range AG side :=
  eapply agree_sub; [exact AG|]; cbv beta;
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; side Hx.
Ltac static_out side :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  let H1 := fresh "HSB" in let H2 := fresh "HSL" in
  pose proof (client_static_below a Ha) as H1; pose proof (client_static_lo a Ha) as H2; unfold SEGTOP_A in H1;
  let Hx := fresh "Hx" in
  assert (Hx : 65536 <= a < 6598656) by (clear - H1 H2; lia); clear H1 H2; cbn [outside]; side Hx.

(* [comment removed for export] *)
Ltac loop_transport m m' MU' side :=
  lazymatch type of MU' with munch ?W' m m' =>
    let AG := fresh "AGL" in
    pose proof (agree_of_munch W' m m' (outside W') MU' (fun x H => H)) as AG;
    repeat match goal with
    | H : LIBH m |- _ =>
        first [ match goal with GP : rt_gaps ?RT |- _ => apply (fun h => LIBH_agree RT GP _ m m' h AG ltac:(static_out side)) in H end
              | idtac "note: loop_transport drops LIBH"; clear H ]
    | H : io_ssp m |- _ =>
        first [ match goal with GP : rt_gaps ?RT, A : ART ?RT ?S m' |- _ =>
                  apply (fun h => io_ssp_agree RT GP _ S m m' h A AG ltac:(static_out side)) in H end
              | idtac "note: loop_transport drops io_ssp"; clear H ]
    | H : rw_cells asegs m ?A ?cs |- _ =>
        first [ apply (rw_cells_agree_nw asegs m m' A cs) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : ro_cells asegs m ?A ?cs |- _ =>
        first [ apply (ro_cells_agree asegs m m' A cs) in H; [ | solve [out_range AG side] ] | clear H ]
    | H : bytes_at asegs m ?A ?bs |- _ =>
        first [ apply (bytes_at_agree asegs m m' A bs) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : wr_at asegs m ?A ?n |- _ =>
        first [ apply (wr_at_agree_nw asegs m m' A n) in H; [ | solve [out_range AG side] ] | clear H ]
    | H : stk asegs m ?lo ?hi |- _ =>
        first [ apply (stk_agree_nw asegs m m' lo hi) in H; [ | solve [out_range AG side] ]
              | idtac "note: loop_transport drops" H; clear H ]
    | H : wmono asegs ?m0 m |- _ =>
        match goal with WMx : wmono asegs m m' |- _ => apply (fun h => wmono_trans asegs m0 m m' h WMx) in H end
    | H : munch ?W ?m0 m |- _ =>
        first [ apply (fun h => munch_trans W m0 m m' h
                         (munch_weaken W' W m m' ltac:(subfp_tac) MU')) in H
              | idtac "note: loop_transport drops (footprint of the loop not inside)" H; clear H ]
    | H : accok _ _ m _ _ |- _ => idtac "note: loop_transport drops accok fact" H; clear H
    | H : acc asegs m _ _ |- _ => clear H
    | H : shk m _ _ |- _ => clear H
    | H : mem_inv asegs m |- _ => clear H
    end;
    clear AG
  end.

(* [comment removed for export] *)
Ltac loop_art RT AF S m' spz MU' ivt :=
  lazymatch type of MU' with munch ?W' ?mm m' =>
    lazymatch goal with
    | A : ART RT S ?m0, MUx : munch ?W ?m0 mm, WMx : wmono asegs ?m0 mm, WMl : wmono asegs mm m' |- _ =>
        let N := fresh "ARTl" in
        assert (N : ART RT S m')
          by (apply (art_client_writes RT AF S m0 m' spz W A
                       (munch_trans W m0 mm m' MUx (munch_weaken W' W mm m' ltac:(subfp_tac) MU'))
                       (wmono_trans asegs m0 mm m' WMx WMl));
              [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | ivt ])
    end
  end.

(* [comment removed for export] *)
Ltac fframe_open RT AF PF live0 usp k SZ getacl :=
  lazymatch goal with H : rt_frames RT ?S = (?f, k) :: ?frs0 |- _ =>
    let FRS := fresh "FRS" in rename H into FRS;
    let fr := fresh "fr" in set (fr := f) in *;
    change (fs_size k) with SZ in *;
    let sz8 := eval vm_compute in (SZ - 8)%Z in let szs := eval vm_compute in (SZ / 8)%Z in
    change (SZ - 8)%Z with sz8 in *; change (SZ / 8)%Z with szs in *;
    let FRM := fresh "FRM" in let FSH := fresh "FSH" in
    lazymatch goal with Hw : wr_at asegs ?mm fr sz8 |- _ =>
      let jf := fresh "jf" in destruct (wr_at_rw_CB mm fr sz8 Hw ltac:(lia)) as (jf & FRM); clear Hw end;
    lazymatch goal with Hw : wr_at asegs ?mm (shad fr) szs |- _ =>
      let js := fresh "js" in destruct (wr_at_rw_CB mm (shad fr) szs Hw ltac:(lia)) as (js & FSH); clear Hw end;
    let n8 := eval vm_compute in (Z.to_nat sz8) in let ns := eval vm_compute in (Z.to_nat szs) in
    change (Z.to_nat sz8) with n8 in FRM; change (Z.to_nat szs) with ns in FSH;
    lazymatch goal with A : ART RT S ?mm |- cps _ (ASTA RT S _ _) _ =>
      let FR0 := fresh "FR0" in let FRHI := fresh "FRHI" in let FR64 := fresh "FR64" in let FRSEG := fresh "FRSEG" in let FRSH := fresh "FRSH" in
      pose proof (af_frames_range RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (FR0 & FRHI & _ & _);
      pose proof (af_frames_align RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (FR64 & FRSEG);
      pose proof (af_frames_hi RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as FRSH;
      change (fs_size k) with SZ in FRHI, FRSH;
      repeat match goal with E : rt_sp0 RT _ = _ |- _ => rewrite E in FRHI end;
      unfold STACK_WIN, SEGTOP_A in FRHI, FRSEG;
      let NFA := fresh "NFA" in
      assert (NFA : forall a, PF a -> (a < fr \/ fr + SZ <= a) /\ (a < shad fr \/ shad (fr + SZ) <= a))
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            apply (new_frame_apart RT AF S mm fr k frs0 live0 usp a A FRS);
            [ let e := fresh "e" in let He := fresh "He" in intros e He;
              repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
            | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
            | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
            | getacl Ha ])
    end
  end.

(* [comment removed for export] *)
Ltac fframe_chunk RT AF fr k SZ p n :=
  match goal with
  | A : ART RT ?S ?mm, FRS : rt_frames RT ?S = (fr, k) :: _ |- _ =>
      let IN := fresh "IN" in
      assert (IN : In (p, n) (rt_live RT S)) by (solve [in_live_tac]);
      let D1 := fresh "FCD" in let D2 := fresh "FCS" in
      pose proof (af_frames_range RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (_ & _ & _ & D1);
      specialize (D1 p n IN);
      pose proof (af_fshadow_apart RT AF S mm fr k A ltac:(rewrite FRS; left; reflexivity)) as (D2 & _);
      specialize (D2 p n IN);
      change (fs_size k) with SZ in D1, D2; unfold shad, SHB in D2; clear IN
  end.
(* [comment removed for export] *)
Ltac fframe_optr RT AF fr k SZ OWN usp :=
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    match goal with
    | A : ART RT ?S ?mm, FRS : rt_frames RT ?S = (fr, k) :: ?frs0 |- _ =>
        let D1 := fresh "FOD" in let D2 := fresh "FOE" in
        assert (D1 : forall x, a <= x < a + n -> (x < fr \/ fr + SZ <= x) /\ (x < shad fr \/ shad (fr + SZ) <= x))
          by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
              apply (new_frame_apart RT AF S mm fr k frs0 lv usp x A FRS);
              [ let e := fresh "e" in let He := fresh "He" in intros e He;
                repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He
              | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; lia
              | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
              | exact (accok_aclient lv frs m0 usp a n x OWN Hx) ]);
        pose proof (D1 a ltac:(lia)) as D2; specialize (D1 (a + n - 1) ltac:(lia));
        unfold shad, SHB in D1, D2
    end
  end.

(* [comment removed for export] *)
Module LC1.
  Import Ltac2.
  Ltac2 rec subset (xs : ident list) (ys : ident list) : bool :=
    match xs with
    | [] => true
    | x :: xs' => if List.exist (Ident.equal x) ys then subset xs' ys else false
    end.
  Ltac2 prune_sub () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then (if SF2.clean bad ty then true else subset (SF2.vars_of [] ty) gv)
                              else subset (SF2.vars_of [] ty) gv).
  Ltac2 prune_sub1 () : unit := Control.enter prune_sub.
End LC1.
Ltac zify_prune_sub := ltac2:(LC1.prune_sub1 ()).
Ltac tlia ::= sf_clear_big;
              first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ zify_prune_sub; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Definition parked (P : Prop) : Prop := P.
Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Ltac unpark H := unfold parked in H.
Ltac clear_acc := repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac unpark_accok OWN AGF :=
  unpark OWN;
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    lazymatch type of AGF with agree_on _ m0 ?m1 =>
      apply (fun h => accok_keep_sub lv frs m0 m1 _ _ _ a n h AGF ltac:(lia) ltac:(auto)) in OWN
    end end.
(* [comment removed for export] *)
Ltac unpark_accok_munch OWN MU live frames usp side :=
  unpark OWN;
  lazymatch type of OWN with accok ?lv ?frs ?m0 ?a ?n =>
    lazymatch type of MU with munch ?W m0 ?m1 =>
      apply (fun h => accok_keep_sub lv frs m0 m1 live frames usp a n h
                        (agree_of_munch W m0 m1 (aclient live frames usp) MU
                           ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; side Hx))
                        ltac:(lia) ltac:(auto)) in OWN
    end end.

(* [comment removed for export] *)
Ltac park_disj :=
  repeat match goal with
  | H : (?A /\ ?B) |- _ => lazymatch A with (_ \/ _) => destruct H | _ => lazymatch B with (_ \/ _) => destruct H end end
  end;
  repeat match goal with
  | H : ?T |- _ => lazymatch T with (?A \/ ?B) => lazymatch type of A with Prop => lazymatch A with
        | context [Z.le] => change T with (parked T) in H | context [Z.lt] => change T with (parked T) in H end end end
  end.
Ltac unpark_all := repeat match goal with H : parked _ |- _ => unfold parked in H end.
(* [comment removed for export] *)
Ltac tlia ::= sf_clear_big;
              first [ Zify.zify; xlia zchecker
                    | sf_unhide;
                      first [ unpark_all; zify_prune_sub; Zify.zify; xlia zchecker
                            | zify_prune_neg; Zify.zify; xlia zchecker
                            | zify_prune_plain; Zify.zify; xlia zchecker
                            | Zify.zify; xlia zchecker ] ].

(* [comment removed for export] *)
Ltac cwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | br | progress sx32_fix; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac cwalk stops := repeat (tryif at_stop stops then fail else cwalk1).

(* [comment removed for export] *)
Lemma accok_keep_P : forall lv frs (m m' : mem) (P : Z -> Prop) a n, accok lv frs m a n -> agree_on P m m' -> 0 <= n ->
  (forall x, shad a <= x < shad a + (n + 7) / 8 -> P x) -> accok lv frs m' a n.
Proof.
  intros lv frs m m' P a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HP; [left; exact H| right].
  exists f, k. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. apply HP.
  rewrite ushadow_length in Hx by lia. exact Hx.
Qed.

(* [comment removed for export] *)
Section KitC2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_apart : forall Σ (m : mem) p1 n1 p2 n2, ART RT Σ m -> In (p1, n1) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p1 <> p2 ->
  p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
  intros Σ m p1 n1 p2 n2 HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 l2 HA E).
  rewrite E in H2. apply in_app_or in H2. apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2| | right; exact H2].
  exfalso. injection H2 as E1 _. exact (NE E1).
Qed.
End KitC2.
