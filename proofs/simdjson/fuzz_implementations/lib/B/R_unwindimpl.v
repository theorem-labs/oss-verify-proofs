(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_leaves R_unwind_defs R_unwindfast.
Import ListNotations.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).

Lemma chain_cells_weaken : forall W W' (m : mem) f ch,
  (forall a, disjoint_from W a 16 -> disjoint_from W' a 16) -> chain_cells W m f ch -> chain_cells W' m f ch.
Proof.
  intros W W' m f ch HW. revert f. induction ch as [|[ra fp] ch IH]; intros f H; cbn in *; [exact I|].
  destruct H as (H1 & H2 & H3 & H4). split; [exact H1| split; [exact H2| split; [apply HW; exact H3| apply IH; exact H4]]].
Qed.

Definition unwind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B bp lo : Z) (tr : list Z) (tb : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(B + 8, B + 12); (B + 16, B + 2064); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m'
    /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ u64arr bsegs m' (B + 16) (wr_trace tr tb)
    /\ rw_cells bsegs m' (B + 2056) [C8 (Z_to_bv 64 bp)]
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition unw_W (B sp : Z) : list (Z * Z) := [(B + 8, B + 12); (B + 16, B + 2064); (sp - 64, sp)]%Z.

Lemma unwind_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B pc bp top bot maxd lo : Z) (ch : list (Z * Z)) (tb : list word) (szw tfb : word)
    (tr : list Z),
  (0 <= B /\ B + 2064 <= 2^63)%Z -> (0 <= pc < 2^64)%Z -> (0 <= bp < 2^64)%Z -> (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  (2 <= maxd <= 255)%Z -> length tb = 255%nat ->
  unwind_trace pc 4096 bot top maxd bp ch = Some tr ->
  chain_cells (unw_W B (bv_unsigned sp)) m bp ch ->
  rw_cells bsegs m 0x17fea8 [C8 (Z_to_bv 64 0x219420)] -> rw_cells bsegs m 0x219420 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (B + 8) [C4 szw] -> u64arr bsegs m (B + 16) tb -> rw_cells bsegs m (B + 2056) [C8 tfb] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= B)%Z -> (0x6e0000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (unwind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B bp lo tr tb m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 maxd) (Z_to_bv 64 pc) (Z_to_bv 64 bp) a4
             (Z_to_bv 64 top) (Z_to_bv 64 bot) (Z_to_bv 64 1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 unwind_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros HB Hpc Hbp Hbt Htop Hmaxd Htb HTR CC G1 G3 SZ TB TF ST HLO HSP HIMG MI.
  unfold unwind_entry, unw_W in *.
  pose proof (munch_refl [(B + 8, B + 12); (B + 16, B + 2064); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply box in CC.
  carve_frame 64%nat ST.
  zhide.
  do 8 zstep.
  do 7 zstep.
  assert (EB : Z.land (Z.land (Z.b2z (maxd <? 1) + -1) 18446744073709551615) bp = bp).
  { rewrite (proj2 (Z.ltb_ge maxd 1)) by lia.
    replace (Z.land (Z.b2z false + -1) 18446744073709551615) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity. }
  rewrite EB in *. clear EB.
  zstep. ifF.
  zstep. ifT.
  zstep. ifT.
  do 13 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (chain_cells_frame _ m mm _ _ (unbox _ CC) MU WM) as CCm;
    apply (chain_cells_weaken _ (uwf_entry_W B (bv_unsigned sp))) in CCm;
      [| intros a HDa; unfold uwf_entry_W; cbn [disjoint_from] in *; lia] end.
  eapply evt_mono; [eapply unwindfast_spec; try eassumption; try lia |].
  intros ms' PO. unfold uwf_post in PO. destruct_exs PO. destruct PO as (E & MU2 & WM2 & MI2 & SZ2 & TB2 & ST2). subst ms'.
  unfold unwind_post.
  do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia]|].
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|]. split; [exact SZ2|]. split; [exact TB2|].
  split; [| exact ST2].
  lazymatch goal with H : rw_cells bsegs ?mm (B + 2056) [C8 (Z_to_bv 64 bp)] |- _ =>
    apply (rw_cells_transport bsegs _ mm _ _ _ H MU2 WM2); cbn [disjoint_from]; simpl_sizes; lia end.
Qed.

Definition unwindimpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B T bp lo : Z) (tr : list Z) (tb : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(B + 8, B + 12); (B + 16, B + 2064); (T + 3168, T + 3169); (bv_unsigned sp - 144, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ u64arr bsegs m' (B + 16) (wr_trace tr tb)
    /\ rw_cells bsegs m' (B + 2056) [C8 (Z_to_bv 64 bp)]
    /\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition uwi_W (B T sp : Z) : list (Z * Z) := [(B + 8, B + 12); (B + 16, B + 2064); (T + 3168, T + 3169); (sp - 144, sp)]%Z.

Lemma unwindimpl_spec : forall ra sp gp t0 t1 t2 s0 s1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B pc bp top bot maxd lo TCX T : Z) (ch : list (Z * Z)) (tb : list word)
    (szw tfb : word) (tr : list Z),
  (0 <= B /\ B + 2064 <= 2^63)%Z -> (0 <= pc < 2^64)%Z -> (0 <= bp < 2^64)%Z -> (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  (2 <= maxd <= 255)%Z -> length tb = 255%nat ->
  unwind_trace pc 4096 bot top maxd bp ch = Some tr ->
  chain_cells (uwi_W B T (bv_unsigned sp)) m bp ch ->
  rw_cells bsegs m 0x17fea8 [C8 (Z_to_bv 64 0x219420)] -> rw_cells bsegs m 0x219420 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T /\ T + 4096 <= 0x10000 \/ 0x6e0000 <= T)%Z -> (T + 4096 <= lo)%Z ->
  (TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
  stack_cells T top bot m -> rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (B + 8) [C4 szw] -> u64arr bsegs m (B + 16) tb -> rw_cells bsegs m (B + 2056) [C8 tfb] ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= B)%Z -> (0x6e0000 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (unwindimpl_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B T bp lo tr tb m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 pc) (Z_to_bv 64 bp) a3 (Z_to_bv 64 1)
             (Z_to_bv 64 maxd) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 unwindimpl_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. intros HB Hpc Hbp Hbt Htop Hmaxd Htb HTR CC G1 G3 AI TC HTCX HTCXl HT HTl HTT SC UW SZ TB TF ST HLO HSP HIMG MI.
  unfold unwindimpl_entry, uwi_W, g_asan_inited in *.
  destruct TC as [(KI & K & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  destruct SC as [SC1 SC2]. unfold off_t_stack_top, off_t_stack_switching in *.
  pose proof (munch_refl [(B + 8, B + 12); (B + 16, B + 2064); (T + 3168, T + 3169); (bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply box in CC.
  carve_frame 80%nat ST.
  zhide.
  zidle_begin sp 80%Z MUz WMz.
  do 11 zstep.
  zidle_end MUz WMz.
  do 7 zstep.
  zstep.
  call (asan_inited_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _).
  all: try (unfold g_asan_inited; assumption); try assumption.
  zstep. ifF.
  zstep.
  sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [assumption| split; [assumption| split; assumption]]| assumption]. }
  all: rewrite ?Esp in *; try lia; try assumption.
  zstep. ifF.
  do 5 (zstep; fix_lit_store). ifF.
  do 2 zstep.
  call (stack_top_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ T top bot).
  1:{ unfold stack_cells, off_t_stack_top, off_t_stack_switching. split; assumption. }
  all: try lia; try assumption.
  do 3 zstep.
  call (stack_bottom_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ T top bot).
  1:{ unfold stack_cells, off_t_stack_top, off_t_stack_switching. split; assumption. }
  all: try lia; try assumption.
  zstep. zstep. ifF.
  do 9 zstep.
  replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp - 80)%Z in * by lia.
  sp_facts.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (chain_cells_frame _ m mm _ _ (unbox _ CC) MU WM) as CCm;
    apply (chain_cells_weaken _ (unw_W B (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80))))) in CCm;
      [| intros a HDa; unfold unw_W; rewrite ?Esp0, ?Esp1, ?Esp; cbn [disjoint_from] in *; lia] end.
  call (unwind_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ B pc bp top bot maxd lo ch tb _ _ tr).
  all: rewrite ?Esp, ?Esp0, ?Esp1 in *; try lia; try eassumption.
  zstep; fix_lit_store.
  do 11 zstep.
  replace (bv_unsigned sp - 80 + 80)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep.
  finish.
Qed.
