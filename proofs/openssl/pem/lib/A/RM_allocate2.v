(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_depot_defs R_depot_put R_poison R_asan_defs R_allocate1 R_allocate2 RM_allocate1.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
Open Scope bv_scope.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_end m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call_fast asegs m mm MU WM end end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition hb1_64 (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 64.
Lemma land63_mod : forall x, (0 <= x)%Z -> Z.land x 63 = (x mod 64)%Z.
Proof. intros x Hx. change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition allocate_p2a_post64 (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (n AB B T : Z) (hdr : list byte)
    (D : depot) (BK : list Z) (DNB SSB : Z) (ws rest : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                  (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x19b028) fc None m' (seg_rom asegs)
    /\ munch [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
             (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (AB + rz_size n + -16)
         [CB 1 (firstn 1 hdr); C1 (Z_to_bv 8 (hb1_64 (hdr_b1 hdr))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n);
          C8 (Z_to_bv 64 (snd (depot_put D (map bv_unsigned ws))))]
    /\ depot_rep (fst (depot_put D (map bv_unsigned ws))) BK DNB SSB m'
    /\ u64arr asegs m' (B + 16) (ws ++ rest)
    /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma allocate_p2a_spec64 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o
    (F : bvmap 5 word) fc (m : mem) (n AB B TCX T lo : Z) (hdr : list byte) (D : depot) (BK : list Z) (DNB SSB : Z)
    (ws rest : list word),
  (1 <= n <= 2^31)%Z -> (0xbc6000 <= AB)%Z -> (AB mod 16 = 0)%Z -> (AB mod 64 = 0)%Z -> (rz_size n mod 64 = 0)%Z -> (AB + (needed2 n + 64) <= lo)%Z ->
  rw_cells asegs m (AB + rz_size n - 16) [CB 16 hdr] ->
  alloc_frame64 m (bv_unsigned sp) ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o ->
  rw_cells asegs m T [C8 (Z_to_bv 64 TCX)] -> rw_cells asegs m (TCX + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length ws)))] ->
  u64arr asegs m (B + 16) (ws ++ rest) -> length (ws ++ rest) = 255%nat -> (1 <= Z.of_nat (length ws) <= 254)%Z ->
  depot_ok D DNB SSB lo -> depot_rep D BK DNB SSB m -> (d_tot D + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  In (bkt (depot_hash (map bv_unsigned ws))) BK -> (d_n D + 2 < 2^16)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 224)%Z -> (bv_unsigned sp + 128 <= B)%Z ->
  (B + 2064 <= 2^63)%Z ->
  (AB + (needed2 n + 64) <= T \/ T + 8 <= AB)%Z -> (AB + (needed2 n + 64) <= TCX + 8 \/ TCX + 12 <= AB)%Z ->
  (AB + (needed2 n + 64) <= DNB \/ DNB + 2 ^ 20 <= AB)%Z -> (AB + (needed2 n + 64) <= SSB \/ SSB + 2 ^ 23 <= AB)%Z ->
  (0 < T < 2^63)%Z -> (0 < TCX < 2^63)%Z ->
  (T + 8 <= DNB \/ DNB + 2 ^ 20 <= T)%Z -> (T + 8 <= SSB \/ SSB + 2 ^ 23 <= T)%Z ->
  (TCX + 12 <= DNB \/ DNB + 2 ^ 20 <= TCX + 8)%Z -> (TCX + 12 <= SSB \/ SSB + 2 ^ 23 <= TCX + 8)%Z ->
  (T + 4096 <= 0x10000 \/ 0xbc6000 <= T)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0xbc6000 <= TCX)%Z ->
  mem_inv asegs m ->
  evt asegs (allocate_p2a_post64 sp gp tp F fc n AB B T hdr D BK DNB SSB ws rest lo m)
    (MS (mkR (Z_to_bv 64 0x19af0c) sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 64) (Z_to_bv 64 (needed2 n + 64)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST)
             (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (64))) (Z_to_bv 64 63) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x19af0c) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros Hn HAB HAB16 HAB64 HRZ64 HABl HD FR TC0 TC8 BC TB HL255 Hsz OK REP Hroom HBK Hn2 ST HLO HB HB2 HST HSX HSD HSS HT HTCX
    HTD HTS HXD HXS HT5 HX5 MI.
  apply box in HT5. apply box in HX5.
  pose proof (needed2_range n Hn) as NR. pose proof (rz_size_range n) as RZR. pose proof (needed2_ge n ltac:(lia)) as NG.
  pose proof OK as (HF & Hn' & Ht & HD1 & HD2 & HS1 & HS2 & HDS).
  unfold alloc_frame64 in FR. apply box in REP.
  remember (AB + rz_size n)%Z as UB eqn:EUB.
  replace (UB - 16)%Z with (UB + -16)%Z in HD by lia.
  pose proof (munch_refl [(UB + -16, UB); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
             (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(UB + -16, UB); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MUh.
  pose proof (wmono_refl asegs m) as WM.
  zhide.
  do 2 zstep. ifF.
  do 4 zstep.
  pose proof (rz_size_mod16 n) as RZ16.
  rewrite land63_mod by lia. replace ((AB + rz_size n) mod 64)%Z with 0%Z by (Z.div_mod_to_equations; lia).
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
  pose proof (munch_refl [(UB + -16, UB)]%Z mm) as MUd; pose proof (wmono_refl asegs mm) as WMd.
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

