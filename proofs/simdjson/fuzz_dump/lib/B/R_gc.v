(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_leaves R_cache_defs R_fs_defs R_fs_ok R_tlsgetaddr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.

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

Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | clear_big; repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].

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

Local Ltac zidle_na H A a := tryif constr_eq A a then idtac else zidle1 H.
Local Ltac zidle_begin_at a n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(a, a + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_na H A a
    | H : ro_cells segs m ?A _ |- _ => zidle_na H A a
    | H : u8arr segs m ?A _ |- _ => zidle_na H A a
    | H : u32arr segs m ?A _ |- _ => zidle_na H A a
    | H : u64arr segs m ?A _ |- _ => zidle_na H A a
    | H : bytes_at segs m ?A _ |- _ => zidle_na H A a
    | H : u8ro segs m ?A _ |- _ => zidle_na H A a
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
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma gc_scan : forall (k : nat) (j B n sh : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  u8arr bsegs m B (repeat (b8 0) (Z.to_nat n)) -> 0 <= sh <= 14 -> n = 2 ^ sh -> 0 <= j -> j + Z.of_nat (S k) = n -> 0 <= B -> B + n < 2 ^ 64 ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a0' a1' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sh) s4 s5 s6 s7 (Z_to_bv 64 B) s9 s10 (Z_to_bv 64 n) t3 t4 t5 t6)
               F (Z_to_bv 64 0x64294) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 sh) s4 s5 s6 s7 (Z_to_bv 64 B) s9 s10 (Z_to_bv 64 j) t3 t4 t5 t6)
        F (Z_to_bv 64 0x64304) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros j B n sh ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 F fc m FL Hsh Hn Hj Hk HB0 HB1 MI.
  - pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
    assert (EUj : bv_unsigned (Z_to_bv 64 j) = j) by (apply unsigned_lit; lia).
    assert (EUBj : bv_unsigned (Z_to_bv 64 (B + j)) = B + j) by (apply unsigned_lit; lia).
    assert (EUj1 : bv_unsigned (Z_to_bv 64 (j + 1)) = j + 1) by (apply unsigned_lit; lia).
    assert (EUsh : bv_unsigned (Z_to_bv 64 sh) = sh) by (apply unsigned_lit; lia).
    zstep.
    pose proof (u8arr_read bsegs m B (repeat (b8 0) (Z.to_nat n)) j (b8 0) (Z_to_bv 64 (B + j)) FL) as RD.
    rewrite nth_error_repeat in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
    zstep. ifT.
    zstep. zstep.
    replace (j + 1) with n by lia.
    assert (SR : Z.shiftr n sh = 1) by (subst n; rewrite Z.shiftr_div_pow2, Z.div_same by lia; reflexivity).
    rewrite (Z.mod_small sh 64) by lia. rewrite SR.
    zstep. ifT.
    apply evt_done. do 2 eexists. reflexivity.
  - pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (EUB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
    assert (EUj : bv_unsigned (Z_to_bv 64 j) = j) by (apply unsigned_lit; lia).
    assert (EUBj : bv_unsigned (Z_to_bv 64 (B + j)) = B + j) by (apply unsigned_lit; lia).
    assert (EUj1 : bv_unsigned (Z_to_bv 64 (j + 1)) = j + 1) by (apply unsigned_lit; lia).
    assert (EUsh : bv_unsigned (Z_to_bv 64 sh) = sh) by (apply unsigned_lit; lia).
    zstep.
    pose proof (u8arr_read bsegs m B (repeat (b8 0) (Z.to_nat n)) j (b8 0) (Z_to_bv 64 (B + j)) FL) as RD.
    rewrite nth_error_repeat in RD by lia. specialize (RD eq_refl ltac:(lia) eq_refl).
    zstep. change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (b8 0)) with (Z_to_bv 64 0).
    zstep. ifT.
    zstep. zstep.
    assert (SR : Z.shiftr (j + 1) sh = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
    rewrite (Z.mod_small sh 64) by lia. rewrite SR.
    zstep. ifF.
    apply (IH (j + 1) B n sh); try assumption; lia.
Qed.

Lemma fl_range : forall FSB c, 0 <= c <= 10 -> FSB + 4096 <= fl_base FSB c /\ fl_base FSB c + NF c <= FSB + 36864.
Proof.
  intros FSB c Hc. unfold fl_base, flags_off, NF.
  assert (E : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  pose proof (Z.pow_le_mono_r 2 4 (14 - c) ltac:(lia) ltac:(lia)) as L1. pose proof (Z.pow_le_mono_r 2 (14 - c) 14 ltac:(lia) ltac:(lia)) as L2.
  change (2 ^ 4) with 16 in L1. change (2 ^ 14) with 16384 in L2. lia.
Qed.

Local Ltac amem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Local Ltac lit_store :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?c)) _) =>
    change (Z_to_le_bytes 8 c) with (le8 (Z_to_bv 64 c)); mem_after_store end.

Local Ltac gc_flags FL c B N U :=
  let mm := amem in
  lazymatch type of FL with forall c0 : Z, _ -> u8arr _ ?m0 _ _ =>
  lazymatch goal with MU : munch ?W m0 mm, WM : wmono _ m0 mm |- _ =>
    let U' := fresh "U'" in
    pose proof (FL c ltac:(lia)) as U'; unfold fl_base, flags_off, NF in U';
    lazymatch type of U' with u8arr _ _ ?B' (repeat _ (Z.to_nat ?N')) =>
      replace B' with B in U' by (cbn; lia); replace N' with N in U' by (cbn; lia) end;
    assert (U : u8arr bsegs mm B (repeat (b8 0) (Z.to_nat N)))
      by (apply (u8arr_transport bsegs W m0 mm B _ U' MU WM); cbn [disjoint_from fst snd];
          rewrite repeat_length, Z2Nat.id by lia; clear_big; lia);
    clear U'
  end end.

Local Ltac gc_class FL c B N SH U :=
  do 16 zstep; lit_store; zstep;
  gc_flags FL c B N U;
  eapply evt_cut;
  [ eapply (gc_scan (Z.to_nat (N - 1)) 0 _ N SH);
    [ lazymatch goal with |- u8arr _ _ ?B' _ => replace B' with B by lia end; exact U
    | lia | reflexivity | lia | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia | clear_big; lia | clear_big; lia | assumption ]
  | clear U; intros ? (? & ? & ->); zstep; zstep; zstep ].

Definition gc_entry : Z := 0x641d0.

Definition gc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FSB lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (FSB + 0x60, FSB + 0x61)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (FSB + 0x58) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)].

Lemma gc_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (rs : word) (FSB TCX T top bottom lo : Z) (g : byte) (gfl : word),
  thread_cells TCX T m -> stack_cells T top bottom m -> 0 <= bottom < top -> bottom <= bv_unsigned rs <= top -> top < 2 ^ 63 ->
  0 < TCX -> TCX + 0xa0 <= lo -> 0 < T -> T + 4096 <= lo ->
  rw_cells bsegs m (FSB + 0x58) [C8 (Z_to_bv 64 20); C1 g] ->
  (forall c, 0 <= c <= 10 -> u8arr bsegs m (fl_base FSB c) (repeat (b8 0) (Z.to_nat (NF c)))) ->
  m2s_cells m -> ro_cells bsegs m 0x16e1c8 [C8 gfl] ->
  0x6cd000 <= FSB -> FSB + 0xb09000 <= lo ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 160 -> 0x6cd000 <= lo -> bv_unsigned sp < 2 ^ 63 ->
  mem_inv bsegs m ->
  evt bsegs (gc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 FSB) rs a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until gfl. intros TC SC B0 RS TOP X0 XL T0 TL FC FL M2S GF F0 FL0 ST LO LO6 SPH MI.
  unfold gc_entry, tpA in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia).
  destruct TC as ((KI & K & TS & TX0) & TX). unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, TX0.
  destruct SC as [S1 S2]. unfold off_t_stack_top, off_t_stack_switching in S1, S2.
  destruct M2S as (M2a & M2b & M2c).
  pose proof (munch_refl [(usp - 160, usp); (FSB + 0x60, FSB + 0x61)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 104%nat ST. rename FR into FRs.
  carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST.
  do 16 zstep. zstep. sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1: exact (conj (conj KI (conj K (conj TS TX0))) TX).
  all: rewrite ?EU144 in *; try lia; try eassumption.
  rename POST into ST.
  zstep. ifF. zstep. zstep.
  call (stack_top_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ T top bottom).
  1: exact (conj S1 S2).
  all: try lia; try eassumption.
  zstep. zstep. zstep.
  call (stack_bottom_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ T top bottom).
  1: exact (conj S1 S2).
  all: try lia; try eassumption.
  assert (EUtop : bv_unsigned (Z_to_bv 64 top) = top) by (apply unsigned_lit; lia).
  assert (EUbot : bv_unsigned (Z_to_bv 64 bottom) = bottom) by (apply unsigned_lit; lia).
  zstep. ifF. zstep. zstep. ifF.

  zstep. zstep. do 6 zstep. zstep.

  zstep. zstep. zstep. lit_store. zstep. zstep. lit_store. zstep. zstep. lit_store. zstep. zstep.
  let mm := amem in
  let bs := eval vm_compute in (option.default [] (image_bytes bsegs 0x10398 8)) in
  assert (RCM : ro_cells bsegs mm 0x10398 [CB (length bs) bs])
    by (apply ro_cells_image; [eassumption| vm_compute; reflexivity| lia| cbn; lia]).
  cbn [length] in RCM.
  zstep. clear RCM.
  do 3 zstep. zstep.

  gc_class FL 0 (FSB + 4096) 16384 14 U0. ifF.

  gc_class FL 1 (FSB + 20480) 8192 13 U1. ifF.

  gc_class FL 2 (FSB + 28672) 4096 12 U2. ifF.

  gc_class FL 3 (FSB + 32768) 2048 11 U3. ifF.

  gc_class FL 4 (FSB + 34816) 1024 10 U4. ifF.

  gc_class FL 5 (FSB + 35840) 512 9 U5. ifF.

  gc_class FL 6 (FSB + 36352) 256 8 U6. ifF.

  gc_class FL 7 (FSB + 36608) 128 7 U7. ifF.

  gc_class FL 8 (FSB + 36736) 64 6 U8. ifF.

  gc_class FL 9 (FSB + 36800) 32 5 U9. ifF.

  gc_class FL 10 (FSB + 36832) 16 4 U10. ifT.

  zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. mem_after_store.

  do 14 zstep.
  release_frame FR3 ST (usp - 136). release_frame FR2 ST (usp - 128). release_frame FR1 ST (usp - 120).
  release_frame FR0 ST (usp - 112). release_frame FR ST (usp - 104). release_frame FRs ST usp.
  zstep.
  apply evt_done. unfold gc_post. rewrite EU.
  do 15 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FC].
Qed.
