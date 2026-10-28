(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_depot_defs R_depot_put R_poison R_asan_defs R_allocate1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
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
Local Ltac zidle_end m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call_fast bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
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
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].

Lemma depot_ok_put_ok : forall D tr DNB SSB lo, depot_ok D DNB SSB lo -> (d_n D + 2 < 2^16)%Z ->
  (d_tot D + Z.of_nat (length tr) + 1 < 2^20)%Z -> depot_ok (fst (depot_put D tr)) DNB SSB lo.
Proof.
  intros D tr DNB SSB lo (HF & Hn & Ht & R) Hn2 Hroom. unfold depot_put.
  destruct (find_of (d_hs D) (depot_hash tr) =? 0); cbn [fst]; [| exact (conj HF (conj Hn (conj Ht R)))].
  unfold depot_ok, d_n in *. cbn [d_hs d_tot]. rewrite app_length. cbn [length].
  split; [apply Forall_app; split; [exact HF| constructor; [apply depot_hash_range| constructor]]|].
  split; [lia| split; [lia| exact R]].
Qed.

Definition hdr_b1 (hdr : list byte) : Z := bv_unsigned (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn 1 hdr))))).
Definition hb1 (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Definition allocate_p2a_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (n AB B T : Z) (hdr : list byte)
    (D : depot) (BK : list Z) (DNB SSB : Z) (ws rest : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                  (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x59390) fc None m' (seg_rom bsegs)
    /\ munch [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
             (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (AB + rz_size n + -16)
         [CB 1 (firstn 1 hdr); C1 (Z_to_bv 8 (hb1 (hdr_b1 hdr))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (snd (depot_put D (map bv_unsigned ws))))]
    /\ depot_rep (fst (depot_put D (map bv_unsigned ws))) BK DNB SSB m'
    /\ u64arr bsegs m' (B + 16) (ws ++ rest)
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma allocate_p2a_spec : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o
    (F : bvmap 5 word) fc (m : mem) (n AB B TCX T lo : Z) (hdr : list byte) (D : depot) (BK : list Z) (DNB SSB : Z)
    (ws rest : list word),
  (1 <= n <= 2^31)%Z -> (0x6cd000 <= AB)%Z -> (AB mod 16 = 0)%Z -> (AB + needed2 n <= lo)%Z ->
  rw_cells bsegs m (AB + rz_size n - 16) [CB 16 hdr] ->
  alloc_frame m (bv_unsigned sp) ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o ->
  rw_cells bsegs m T [C8 (Z_to_bv 64 TCX)] -> rw_cells bsegs m (TCX + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length ws)))] ->
  u64arr bsegs m (B + 16) (ws ++ rest) -> length (ws ++ rest) = 255%nat -> (1 <= Z.of_nat (length ws) <= 254)%Z ->
  depot_ok D DNB SSB lo -> depot_rep D BK DNB SSB m -> (d_tot D + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  In (bkt (depot_hash (map bv_unsigned ws))) BK -> (d_n D + 2 < 2^16)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 224)%Z -> (bv_unsigned sp + 128 <= B)%Z ->
  (B + 2064 <= 2^63)%Z ->
  (AB + needed2 n <= T \/ T + 8 <= AB)%Z -> (AB + needed2 n <= TCX + 8 \/ TCX + 12 <= AB)%Z ->
  (AB + needed2 n <= DNB \/ DNB + 2 ^ 20 <= AB)%Z -> (AB + needed2 n <= SSB \/ SSB + 2 ^ 23 <= AB)%Z ->
  (0 < T < 2^63)%Z -> (0 < TCX < 2^63)%Z ->
  (T + 8 <= DNB \/ DNB + 2 ^ 20 <= T)%Z -> (T + 8 <= SSB \/ SSB + 2 ^ 23 <= T)%Z ->
  (TCX + 12 <= DNB \/ DNB + 2 ^ 20 <= TCX + 8)%Z -> (TCX + 12 <= SSB \/ SSB + 2 ^ 23 <= TCX + 8)%Z ->
  (T + 4096 <= 0x10000 \/ 0x6cd000 <= T)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0x6cd000 <= TCX)%Z ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p2a_post sp gp tp F fc n AB B T hdr D BK DNB SSB ws rest lo m)
    (MS (mkR (Z_to_bv 64 0x59274) sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST)
             (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x59274) fc None m (seg_rom bsegs)).
Proof.
  intros until rest. intros Hn HAB HAB16 HABl HD FR TC0 TC8 BC TB HL255 Hsz OK REP Hroom HBK Hn2 ST HLO HB HB2 HST HSX HSD HSS HT HTCX
    HTD HTS HXD HXS HT5 HX5 MI.
  apply box in HT5. apply box in HX5.
  pose proof (needed2_range n Hn) as NR. pose proof (rz_size_range n) as RZR. pose proof (needed2_ge n ltac:(lia)) as NG.
  pose proof OK as (HF & Hn' & Ht & HD1 & HD2 & HS1 & HS2 & HDS).
  unfold alloc_frame in FR. apply box in REP.
  remember (AB + rz_size n)%Z as UB eqn:EUB.
  replace (UB - 16)%Z with (UB + -16)%Z in HD by lia.
  pose proof (munch_refl [(UB + -16, UB); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
             (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(UB + -16, UB); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MUh.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  do 2 zstep. ifF.
  do 4 zstep.
  pose proof (rz_size_mod16 n) as RZ16.
  rewrite land7_mod by lia. replace ((AB + rz_size n) mod 8)%Z with 0%Z by (Z.div_mod_to_equations; lia).
  ifT.
  do 2 zstep. ifF.
  rewrite <- EUB.
  do 6 zstep. zstep. sb_fix.
  assert (E32 : Z.shiftr n 32 = 0%Z) by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
  assert (E48 : Z.shiftr n 48 = 0%Z) by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
  rewrite E32, E48.
  zstep; fix_lit_store.
  zstep; fix_lit_store.
  zstep. dIf_closed.
  do 5 zstep. sb_fix.
  zstep. ifF.
  do 3 zstep.
  change (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 0))) 32) with 0%Z.
  do 4 zstep.
  clear TC0 TC8 HST HSX HTD HTS HXD HXS.
  let mm := amem in
  pose proof (depot_rep_frame D BK DNB SSB lo _ m mm (unbox _ REP) OK MUh WM ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)) as REPm.
  clear MUh.
  call (depot_put_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ D BK DNB SSB (B + 16)%Z lo ws rest).
  all: try (arith_goal; lia); try eassumption.
  let mm := amem in
  pose proof (munch_refl [(UB + -16, UB)]%Z mm) as MUd; pose proof (wmono_refl bsegs mm) as WMd.
  assert (RID : (0 <= snd (depot_put D (map bv_unsigned ws)) < 2^16)%Z).
  { pose proof (depot_put_id D (map bv_unsigned ws)) as P. pose proof (depot_put_n D (map bv_unsigned ws)) as P2.
    destruct (depot_put D (map bv_unsigned ws)) as [D' id] eqn:E. cbn [fst snd] in *. unfold d_n in *. lia. }
  do 2 zstep.
  assert (EZ : Z.shiftr (Z.land (Z.shiftl (snd (depot_put D (map bv_unsigned ws))) 32) 18446744073709551615) 32
               = snd (depot_put D (map bv_unsigned ws))).
  { rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
  rewrite ?EZ.
  assert (EZ2 : Z.land (snd (depot_put D (map bv_unsigned ws))) 4294967295 = snd (depot_put D (map bv_unsigned ws))).
  { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  rewrite EZ2.
  zstep. rewrite ?Z.lor_0_l.
  zstep.
  subst UB.
  finish.
  lazymatch goal with H : depot_rep _ BK DNB SSB ?m2 |- depot_rep _ BK DNB SSB ?mm =>
    apply (depot_rep_frame _ BK DNB SSB lo _ m2 mm H (depot_ok_put_ok D (map bv_unsigned ws) DNB SSB lo OK Hn2 ltac:(rewrite map_length; lia)) MUd WMd);
      cbn [disjoint_from]; lia end.
Qed.

Definition size_rd (n : Z) : Z := 8 * (n / 8).

Definition allocate_p2_exit (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (n AB B T : Z) (s0v s3v s9v : word) (m : mem) (W : list (Z * Z))
    (lo : Z) (P : mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (m' : mem),
    (if 8 <=? n then
       exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR (Z_to_bv 64 0x5948c) sp gp tp t0' t1' t2' s0v (Z_to_bv 64 n) (Z_to_bv 64 (AB + rz_size n))
                     (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 0) a3' a4' a5' a6' a7' (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n))
                     (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 B) (Z_to_bv 64 0)
                     s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                F (Z_to_bv 64 ps_entry) fc None m' (seg_rom bsegs)
     else
       exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0v (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 AB) s3v
                     (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0) (Z_to_bv 64 B)
                     (Z_to_bv 64 0) s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                F (Z_to_bv 64 0x5948c) fc None m' (seg_rom bsegs))
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ P m' /\ stk bsegs m' lo (bv_unsigned sp).

Ltac finish_exit := apply evt_done; hnf; eexists; split; [repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|];
  repeat match goal with |- _ /\ _ => split end; try exact I; try assumption.

Lemma size_rd_machine : forall n, (0 <= n < 2^48)%Z -> Z.land n (Z.shiftr 18446744073709027328 16) = size_rd n.
Proof.
  intros n Hn. change (Z.shiftr 18446744073709027328 16) with 281474976710648%Z. unfold size_rd.
  assert (E : Z.land n 281474976710648 = Z.land (Z.land n (Z.ones 48)) 18446744073709551608).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
    destruct (Z.lt_ge_cases i 48) as [L|L].
    - rewrite (Z.ones_spec_low 48 i) by lia. rewrite andb_true_r.
      assert (B1 : Z.testbit 281474976710648 i = Z.testbit 18446744073709551608 i).
      { rewrite <- (Z.mod_pow2_bits_low 18446744073709551608 48 i) by lia. reflexivity. }
      rewrite B1. reflexivity.
    - rewrite (Z.ones_spec_high 48 i) by lia. rewrite andb_false_r, !andb_false_l.
      rewrite (Z.bits_above_log2 281474976710648 i) by (try lia; change (Z.log2 281474976710648) with 47%Z; lia).
      apply andb_false_r. }
  rewrite E, Z.land_ones, Z.mod_small by lia. apply land_m8. lia.
Qed.

Lemma allocate_p2P_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra (F : bvmap 5 word) fc (m : mem)
    (n AB B T lo : Z) (sb : byte) (s3v : word),
  (1 <= n <= 2^31)%Z -> (kHighShadowEnd < AB)%Z -> (AB + needed2 n <= 2^47)%Z ->
  rw_cells bsegs m 0x16e1d0 [C8 (Z_to_bv 64 0x177138)] -> rw_cells bsegs m 0x177138 [C8 (Z_to_bv 64 SHB)] ->
  rw_cells bsegs m (shad AB) [C1 sb] -> bv_unsigned sb <> 0%Z -> stk bsegs m lo (bv_unsigned sp) ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p2_exit sp gp tp F fc n AB B T (Z_to_bv 64 1) s3v (Z_to_bv 64 (AB + rz_size n + n)) m [] lo (fun _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x59390) fc None m (seg_rom bsegs)).
Proof.
  intros until s3v. intros Hn HAB HAB2 G0 G1 SHC Hsb ST MI.
  unfold kHighShadowEnd in HAB. pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG.
  pose proof (rz_size_range n) as RZR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zhide.
  zstep. ifF.
  do 5 zstep.
  replace (SHB + Z.shiftr AB 3)%Z with (shad AB) by (unfold shad; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3)%Z with 8%Z; lia).
  remember (shad AB) as SA eqn:ESA.
  pose proof (bv_unsigned_in_range 8 sb) as Rsb. unfold bv_modulus in Rsb. cbn [Z.of_N] in Rsb.
  zstep. zstep. ifT.
  do 3 zstep. rewrite size_rd_machine by lia.
  zstep.
  unfold allocate_p2_exit.
  destruct (8 <=? n) eqn:C8; cbv beta iota.
  - apply Z.leb_le in C8.
    assert (R8 : (8 <= size_rd n <= n)%Z) by (unfold size_rd; Z.div_mod_to_equations; lia).
    ifF. do 4 zstep. finish_exit.
  - apply Z.leb_gt in C8.
    assert (R0 : size_rd n = 0%Z) by (unfold size_rd; rewrite Z.div_small by lia; reflexivity).
    rewrite R0. ifT. finish_exit.
Qed.

Definition sec_ru (n : Z) : Z := 4096 * ((needed2 n + 4095) / 4096).
Definition sec_tb (n AB : Z) : Z := 8 * ((AB + rz_size n + n + 7) / 8).

Lemma land_m4096 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x 18446744073709547520 = (4096 * (x / 4096))%Z.
Proof.
  intros x Hx.
  assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  assert (E2 : Z.ones 64 = Z.lor 18446744073709547520 4095) by reflexivity.
  rewrite E2, Z.land_lor_distr_r in E1.
  pose proof (Z.add_lor_land (Z.land x 18446744073709547520) (Z.land x 4095)) as E3.
  assert (E4 : Z.land (Z.land x 18446744073709547520) (Z.land x 4095) = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
    assert (B : Z.testbit 18446744073709547520 i && Z.testbit 4095 i = false)
      by (rewrite <- Z.land_spec; change (Z.land 18446744073709547520 4095) with 0%Z; apply Z.bits_0).
    destruct (Z.testbit x i), (Z.testbit 18446744073709547520 i), (Z.testbit 4095 i); cbn in *; congruence. }
  rewrite E4, Z.add_0_r, E1 in E3.
  change 4095%Z with (Z.ones 12) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 12)%Z with 4096%Z in E3.
  pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.

Lemma allocate_p2S_tail : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra (F : bvmap 5 word) fc (m : mem)
    (n AB B T lo : Z) (s3v : word) (sj1 sj2 : list byte),
  (1 <= n <= 2^31)%Z -> from_primary n = false -> (AB mod 4096 = 0)%Z ->
  ((0 <= AB - 4096 /\ AB + sec_ru n <= kLowMemEnd + 1) \/ (kHighShadowEnd < AB - 4096 /\ AB + sec_ru n <= kHighMemEnd + 1))%Z ->
  rw_cells bsegs m (g_instance + 0x40) [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed2 n))] ->
  rw_cells bsegs m (shad AB) [CB (Z.to_nat (rz_size n / 8)) sj1] ->
  rw_cells bsegs m (shad (sec_tb n AB)) [CB (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8)) sj2] ->
  ps_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p2_exit sp gp tp F fc n AB B T (Z_to_bv 64 (sec_ru n)) s3v (Z_to_bv 64 (AB + rz_size n + n + 7)) m
               [(shad AB, shad AB + rz_size n / 8); (shad (sec_tb n AB), shad (sec_tb n AB) + (AB + sec_ru n - sec_tb n AB) / 8);
                (bv_unsigned sp - 64, bv_unsigned sp)]%Z lo
               (fun m' => rw_cells bsegs m' (shad AB) [CB (Z.to_nat (rz_size n / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (rz_size n / 8)))]
                          /\ rw_cells bsegs m' (shad (sec_tb n AB))
                               [CB (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8))
                                   (repeat (Z_to_bv 8 250) (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8)))]))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 1522392) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x593ec) fc None m (seg_rom bsegs)).
Proof.
  intros until sj2. intros Hn HFP HAB4 HMAP PGC HDC SH1 SH2 PS ST HLO HLO2 MI.
  pose proof (needed2_range n Hn) as NR. pose proof (needed2_ge n ltac:(lia)) as NG. pose proof (rz_size_range n) as RZR.
  assert (Hbig : (64512 < n)%Z) by (destruct (from_primary_iff n ltac:(lia)) as [_ H]; destruct (Z.le_gt_cases n 64512) as [L|L];
    [rewrite (H L) in HFP; discriminate| lia]).
  assert (RZ2048 : rz_size n = 2048%Z) by (unfold rz_size; rewrite rz_log_big by lia; reflexivity).
  assert (NG2 : (n + 2 * rz_size n <= needed2 n)%Z).
  { unfold needed2, needed. rewrite HFP. pose proof (rounded_range n ltac:(lia)) as (RR1 & _). lia. }
  assert (RRU : (needed2 n <= sec_ru n < needed2 n + 4096 /\ sec_ru n mod 4096 = 0)%Z).
  { unfold sec_ru. split; [Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia]. }
  assert (RTB : (AB + rz_size n + n <= sec_tb n AB <= AB + rz_size n + n + 7 /\ sec_tb n AB mod 8 = 0)%Z).
  { unfold sec_tb. split; [Z.div_mod_to_equations; lia| rewrite Z.mul_comm; apply Z.mod_mul; lia]. }
  unfold kHighShadowEnd, kLowMemEnd, kHighMemEnd, INST, g_instance in *.
  change (1522392 + 64)%Z with 1522456%Z in PGC.
  replace (AB - 4096 + 16)%Z with (AB + -4080)%Z in HDC by lia.
  assert (F1 : (shad AB + rz_size n / 8 <= shad (sec_tb n AB))%Z) by (unfold shad; rewrite RZ2048; Z.div_mod_to_equations; lia).
  assert (F2 : (shad (sec_tb n AB) + (AB + sec_ru n - sec_tb n AB) / 8 <= 17594333495295 + 1)%Z)
    by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (F0 : (2147450880 <= shad AB)%Z) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(shad AB, shad AB + rz_size n / 8); (shad (sec_tb n AB), shad (sec_tb n AB) + (AB + sec_ru n - sec_tb n AB) / 8);
                (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zhide.
  do 3 zstep.
  rewrite Z.land_comm. change 4095%Z with (Z.ones 12). rewrite Z.land_ones, HAB4 by lia.
  zstep. ifF. zstep. zstep. dIf_closed.
  zstep. change (AB + - (4096))%Z with (AB + -4096)%Z.
  do 5 zstep.
  assert (ERU : Z.land (Z.land (needed2 n + Z.ones 12) 18446744073709551615) (Z.land (0 + - (4096)) 18446744073709551615)
                = sec_ru n).
  { change (Z.land (0 + - (4096)) 18446744073709551615) with 18446744073709547520%Z.
    change 18446744073709551615%Z with (Z.ones 64). rewrite (Z.land_ones (needed2 n + Z.ones 12)) by lia.
    change (Z.ones 12) with 4095%Z. rewrite Z.mod_small by lia. rewrite land_m4096 by lia. reflexivity. }
  rewrite ERU.
  do 2 zstep.
  rewrite land_m8 by lia. change (8 * ((AB + rz_size n + n + 7) / 8))%Z with (sec_tb n AB).
  do 4 zstep.
  replace (AB + rz_size n + - AB)%Z with (rz_size n) by lia.
  apply box in SH1. apply box in HDC.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ AB (rz_size n) 250 lo sj1).
  all: try (unfold ps_args_ok, kHighShadowEnd, kLowMemEnd, kHighMemEnd; rewrite ?RZ2048; cbn; lia); try (arith_goal; lia); try eassumption.
  do 4 zstep.
  let mm := amem in
  pose proof (ps_cells_framed m mm _ PS MU WM ltac:(unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia)) as PSm.
  zstep.
  replace (AB + - sec_tb n AB + sec_ru n)%Z with (AB + sec_ru n - sec_tb n AB)%Z by lia.
  apply box in SH2.
  call (poison_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (sec_tb n AB) (AB + sec_ru n - sec_tb n AB)
          250 lo sj2).
  all: try (arith_goal; lia); try eassumption.
  1:{ unfold ps_args_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd. split; [| lia]. split; [lia| split; [| lia]].
      assert (AB mod 8 = 0)%Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  do 3 zstep. rewrite size_rd_machine by lia.
  zstep.
  unfold allocate_p2_exit.
  destruct (8 <=? n) eqn:C8; cbv beta iota; [| apply Z.leb_gt in C8; lia].
  apply Z.leb_le in C8.
  assert (R8 : (8 <= size_rd n <= n)%Z) by (unfold size_rd; Z.div_mod_to_equations; lia).
  ifF. do 4 zstep. finish_exit.
Qed.

Lemma allocate_p2S_spec : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra (F : bvmap 5 word) fc (m : mem)
    (n AB B T SB lo : Z) (s3v : word) (sj1 sj2 : list byte),
  (1 <= n <= 2^31)%Z -> from_primary n = false -> (AB mod 4096 = 0)%Z ->
  (AB + sec_ru n <= SB \/ SB + 2^37 <= AB)%Z ->
  ((0 <= AB - 4096 /\ AB + sec_ru n <= kLowMemEnd + 1) \/ (kHighShadowEnd < AB - 4096 /\ AB + sec_ru n <= kHighMemEnd + 1))%Z ->
  rw_cells bsegs m i_spacebeg [C8 (Z_to_bv 64 SB)] -> rw_cells bsegs m (g_instance + 0x40) [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed2 n))] ->
  rw_cells bsegs m (shad AB) [CB (Z.to_nat (rz_size n / 8)) sj1] ->
  rw_cells bsegs m (shad (sec_tb n AB)) [CB (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8)) sj2] ->
  ps_cells m ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
  (0 < SB < 2^63)%Z ->
  mem_inv bsegs m ->
  evt bsegs (allocate_p2_exit sp gp tp F fc n AB B T (Z_to_bv 64 (sec_ru n)) s3v (Z_to_bv 64 (AB + rz_size n + n + 7)) m
               [(shad AB, shad AB + rz_size n / 8); (shad (sec_tb n AB), shad (sec_tb n AB) + (AB + sec_ru n - sec_tb n AB) / 8);
                (bv_unsigned sp - 64, bv_unsigned sp)]%Z lo
               (fun m' => rw_cells bsegs m' (shad AB) [CB (Z.to_nat (rz_size n / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (rz_size n / 8)))]
                          /\ rw_cells bsegs m' (shad (sec_tb n AB))
                               [CB (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8))
                                   (repeat (Z_to_bv 8 250) (Z.to_nat ((AB + sec_ru n - sec_tb n AB) / 8)))]))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x59390) fc None m (seg_rom bsegs)).
Proof.
  intros until sj2. intros Hn HFP HAB4 HSB HMAP SBC PGC HDC SH1 SH2 PS ST HLO HLO2 HSBr MI.
  assert (RRU : (needed2 n <= sec_ru n)%Z) by (unfold sec_ru; Z.div_mod_to_equations; lia).
  pose proof (needed2_range n Hn) as NR.
  unfold i_spacebeg, INST, g_instance in *. change (1522392 + 32)%Z with 1522424%Z in SBC.
  assert (HAB0 : (0 <= AB < 2^47)%Z) by (unfold kHighShadowEnd, kLowMemEnd, kHighMemEnd in HMAP; lia).
  pose proof (munch_refl [] m) as MU0. pose proof (wmono_refl bsegs m) as WM0.
  zhide.
  zstep. ifT.
  zstep. zstep.
  destruct (Z.ltb_spec AB SB) as [C1|C1].
  - ifT. eapply allocate_p2S_tail; eassumption.
  - ifF. do 4 zstep. ifT. eapply allocate_p2S_tail; eassumption.
Qed.
