(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_small R_cache_defs R_prim_defs R_prim_kit R_depot_defs R_depot_hash R_depot_lock R_depot_store.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma shl44_shr42 : forall x, (0 <= x < 2^64)%Z -> Z.shiftr (Z.land (Z.shiftl x 44) 18446744073709551615) 42 = (4 * bkt x)%Z.
Proof.
  intros x Hx. unfold bkt. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64).
  rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 64)%Z with (2 ^ 20 * 2 ^ 44)%Z by reflexivity. rewrite Z.mul_mod_distr_r by lia.
  replace ((x mod 2 ^ 20) * 2 ^ 44)%Z with ((4 * (x mod 2 ^ 20)) * 2 ^ 42)%Z by lia. apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
Lemma amo32_add_bytes_lit : forall a b, (0 <= a < 2^32)%Z -> (0 <= b < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 a)))) (Z_to_bv 32 b)))
  = le4 (Z_to_bv 64 (a + b)).
Proof.
  intros a b Ha Hb. cbn [amo_val]. rewrite bv_add_unsigned.
  rewrite low32_unsigned, le_bytes_to_word_le4, !Z_to_bv_unsigned.
  unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !(Z.mod_small a (2^64)) by lia. rewrite !(Z.mod_small a (2^32)) by lia. rewrite !(Z.mod_small b (2^32)) by lia.
  rewrite (Z_to_le_bytes_mod 4 (a + b) 32) by lia. rewrite (Z_to_le_bytes_mod 4 (a + b) 64) by lia. reflexivity.
Qed.

Ltac amo32_fix_lit := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD
         (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 ?a)))) (Z_to_bv 32 ?b))))) _) =>
      rewrite (amo32_add_bytes_lit a b) by lia; mem_after_store
  end.

(* [comment removed for export] *)
Section FIND.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (hs : list Z) (h DNB : Z) (Q : machine_state -> Prop).
Hypothesis HF : Forall (fun x => 0 <= x < 2 ^ 64)%Z hs.
Hypothesis Rh : (0 <= h < 2 ^ 64)%Z.
Hypothesis Hn : (Z.of_nat (length hs) + 1 < 2 ^ 16)%Z.
Hypothesis HD : (0xbcb000 <= DNB /\ DNB + 2 ^ 20 <= 2 ^ 63)%Z.
Hypothesis ND : forall i, (1 <= i <= Z.of_nat (length hs))%Z -> exists sid : word,
  rw_cells ctasegs m (DNB + 16 * i) [C8 (Z_to_bv 64 (hash_of hs i)); C4 (Z_to_bv 64 (link_of hs i)); C4 sid].
Hypothesis M1 : rw_cells ctasegs m d_map1 [C8 (Z_to_bv 64 DNB)].
Notation ST pc x10 x11 x12 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 h) s4 s5 (Z_to_bv 64 65535) s7
           (Z_to_bv 64 11878184) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom ctasegs)).
Hypothesis KA : find_of hs h = 0%Z -> forall a0 a2, evt ctasegs Q (ST 0x1e6234 a0 (Z_to_bv 64 0) a2).
Hypothesis KB : find_of hs h <> 0%Z -> forall a1 a2, evt ctasegs Q (ST 0x1e62e0 (Z_to_bv 64 (find_of hs h)) a1 a2).

Lemma find_loop : forall k s a0 a2, (s < Z.of_nat k)%Z -> walk_inv hs h s -> evt ctasegs Q (ST 0x1e61dc a0 (Z_to_bv 64 s) a2).
Proof.
  induction k as [|k IH]; intros s a0 a2 Hk HW; pose proof (walk_range _ _ _ HW) as Rs; [lia|].
  zhide.
  zstep.
  destruct (Z.eq_dec s 0) as [->|Ns].
  - ifT. apply KA. apply walk_zero. exact HW.
  - ifF.
    destruct (ND s ltac:(lia)) as (sid & NC).
    pose proof (hash_of_range hs s HF) as Rhs. pose proof (link_of_range hs s ltac:(lia)) as Rl.
    do 2 zstep.
    assert (E0 : bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 16) = 0%Z).
    { unfold bv_wrap. change (bv_modulus 32) with (2^32)%Z. rewrite Z.mod_small by lia.
      rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
    rewrite E0.
    do 4 zstep. ifF.
    do 5 zstep.
    assert (E1 : Z.shiftl (Z.land (Z.land s 4294967295) 65535) 4 = (16 * s)%Z).
    { change 4294967295%Z with (Z.ones 32). change 65535%Z with (Z.ones 16). rewrite !Z.land_ones by lia.
      rewrite !Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. }
    rewrite E1. remember (DNB + 16 * s)%Z as NA eqn:ENA.
    zstep. zstep. rewrite (sx32_small_A (link_of hs s)) by lia.
    zstep.
    destruct (Z.eq_dec (hash_of hs s) h) as [Eq|Nq].
    + ifF. zstep. rewrite <- (walk_hit _ _ _ HW Ns Eq). apply KB. rewrite (walk_hit _ _ _ HW Ns Eq). exact Ns.
    + ifT. destruct (walk_next _ _ _ HW Ns Nq) as [HW' Rl'].
      apply IH; [lia| exact HW'].
Qed.
End FIND.

(* [comment removed for export] *)
Lemma depot_rep_miss : forall (D : depot) BK DNB SSB lo h sz SL SH (sid : word) (m m' : mem),
  depot_ok D DNB SSB lo -> depot_rep D BK DNB SSB m -> (0 <= h < 2^64)%Z -> (1 <= sz)%Z -> (d_tot D + sz + 1 < 2^20)%Z ->
  (lo <= SL)%Z ->
  munch [(d_tab + 4 * bkt h, d_tab + 4 * bkt h + 4); (d_nuniq, d_nuniq + 4);
         (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1), DNB + 16 * (Z.of_nat (length (d_hs D)) + 1) + 16);
         (s_total, s_total + 8); (s_stored0, s_stored0 + 4); (SSB + 8 * d_tot D, SSB + 8 * (d_tot D + sz + 1)); (SL, SH)]%Z m m' ->
  wmono ctasegs m m' ->
  rw_cells ctasegs m' (d_tab + 4 * bkt h) [C4 (Z_to_bv 64 (Z.of_nat (length (d_hs D)) + 1))] ->
  rw_cells ctasegs m' d_nuniq [C4 (Z_to_bv 64 (Z.of_nat (length (d_hs D)) + 1))] ->
  rw_cells ctasegs m' d_map1 [C8 (Z_to_bv 64 DNB)] ->
  rw_cells ctasegs m' (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1))
    [C8 (Z_to_bv 64 h); C4 (Z_to_bv 64 (tab_of (d_hs D) (bkt h))); C4 sid] ->
  stk ctasegs m' (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1) + 16) (DNB + 2 ^ 20) ->
  rw_cells ctasegs m' s_total [C8 (Z_to_bv 64 (d_tot D + sz + 1))] -> rw_cells ctasegs m' s_data0 [C8 (Z_to_bv 64 SSB)] ->
  rw_cells ctasegs m' s_stored0 [C4 (Z_to_bv 64 (d_tot D + sz + 1))] ->
  stk ctasegs m' (SSB + 8 * (d_tot D + sz + 1)) (SSB + 2 ^ 23) ->
  depot_rep (mkDepot (d_hs D ++ [h]) (d_tot D + sz + 1)) BK DNB SSB m'.
Proof.
  intros D BK DNB SSB lo h sz SL SH sid m m' OK REP Rh Hsz Hroom HSL MU WM BKC NU' M1' NC FS' TT' DT' SD' FF'.
  destruct OK as (HF & Hn & Ht & HD1 & HD2 & HS1 & HS2 & HDS). unfold d_n in Hn.
  destruct REP as (TAB & _ & _ & ND & _ & _ & _ & _ & _).
  assert (Rb : (0 <= bkt h < 2^20)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
  unfold depot_rep, d_n. cbn [d_hs d_tot]. rewrite app_length. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1%Z.
  split; [| split; [exact NU'| split; [exact M1'| split; [| split; [| split; [exact TT'| split; [exact DT'| split; [exact SD'| exact FF']]]]]]]].
  - intros b Hb. destruct (TAB b Hb) as [Rb' C]. split; [exact Rb'|]. rewrite tab_of_snoc.
    destruct (Z.eqb_spec (bkt h) b) as [E|E]; [subst b; exact BKC|].
    apply (rw_cells_transport ctasegs _ m m' _ _ C MU WM). cbn [disjoint_from cells_size csize Nat.add]. lia.
  - intros i Hi. destruct (Z.eq_dec i (Z.of_nat (length (d_hs D)) + 1)) as [->|Ni].
    + exists sid. rewrite hash_of_snoc_new, link_of_snoc_new. exact NC.
    + destruct (ND i ltac:(unfold d_n; lia)) as (sid' & C). exists sid'.
      rewrite hash_of_snoc_old, link_of_snoc_old by lia.
      apply (rw_cells_transport ctasegs _ m m' _ _ C MU WM). cbn [disjoint_from cells_size csize Nat.add]. lia.
  - replace (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1 + 1))%Z with (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1) + 16)%Z by lia.
    exact FS'.
Qed.

(* [comment removed for export] *)
Definition depot_put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D : depot) (BK : list Z) (DNB SSB TR : Z) (ws rest : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd (depot_put D (map bv_unsigned ws)))) a1' a2' a3' a4' a5' a6'
                  a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8); (s_data0, s_stored0 + 4);
             (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 224, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ depot_rep (fst (depot_put D (map bv_unsigned ws))) BK DNB SSB m'
    /\ u64arr ctasegs m' TR (ws ++ rest)
    /\ stk ctasegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma depot_put_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D : depot) (BK : list Z) (DNB SSB TR lo : Z) (ws rest : list word),
  depot_ok D DNB SSB lo -> (1 <= Z.of_nat (length ws) <= 254)%Z -> (d_tot D + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  depot_rep D BK DNB SSB m -> In (bkt (depot_hash (map bv_unsigned ws))) BK -> u64arr ctasegs m TR (ws ++ rest) ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 224)%Z -> (bv_unsigned sp <= TR)%Z ->
  length (ws ++ rest) = 255%nat -> (TR + 2040 <= 2^63)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (depot_put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D BK DNB SSB TR ws rest lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TR) (Z_to_bv 64 (Z.of_nat (length ws))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 depotput_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until rest. intros OK Hsz Hroom REP HBK TB ST HLO HTR HL255 HTR2 MI. unfold depotput_entry.
  remember (Z.of_nat (length ws)) as sz eqn:Esz.
  pose proof OK as (HF & Hn & Ht & HD1 & HD2 & HS1 & HS2 & HDS).
  unfold d_n in Hn.
  remember (depot_hash (map bv_unsigned ws)) as h eqn:Eh.
  assert (Rh : (0 <= h < 2^64)%Z) by (rewrite Eh; apply depot_hash_range).
  pose proof (munch_refl [(d_tab + 4 * bkt h, d_tab + 4 * bkt h + 4); (d_nuniq, d_nuniq + 4);
             (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1), DNB + 16 * (Z.of_nat (length (d_hs D)) + 1) + 16);
             (s_total, s_total + 8); (s_stored0, s_stored0 + 4); (SSB + 8 * d_tot D, SSB + 8 * (d_tot D + sz + 1));
             (bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)]%Z m) as MUs.
  pose proof (wmono_refl ctasegs m) as WM.
  apply box in REP. apply box in TB.
  carve_frame 88%nat ST. carve_frame 16%nat ST. carve_frame 8%nat ST.
  zhide.
  do 8 zstep.
  do 17 zstep. ifT.
  lazymatch goal with H : rw_cells ctasegs _ (bv_unsigned sp + -104)%Z [C8 _; C8 _] |- _ =>
    apply (rw_cells_c8_split _ _ [C8 (Z_to_bv 64 TR)] []) in H; [cbn [app] in H| lia] end.
  do 3 zstep. rewrite Z.add_0_r, bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia). ifF.
  zstep. ifF.
  let mm := curmem in
  pose proof (u64arr_transport ctasegs _ m mm TR (ws ++ rest) (unbox _ TB) MUs WM ltac:(cbn [disjoint_from]; rewrite HL255; lia)) as TBm.
  eapply (hash_frag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TR sz ws rest _ ltac:(lia) ltac:(lia) ltac:(lia) TBm).
  { exact MI. }
  intros a0' a1' a2' a4' a5' a6'.
  rewrite <- Eh.
  do 2 zstep. rewrite shl44_shr42 by lia.
  zstep.
  assert (Rb : (0 <= bkt h < 2^20)%Z) by (unfold bkt; apply Z.mod_pos_bound; lia).
  remember (7683864 + 4 * bkt h)%Z as BA eqn:EBA.
  let mm := curmem in
  destruct (unbox _ REP) as (TAB & _);
  pose proof (rw_cells_transport ctasegs _ m mm _ _ (proj2 (TAB (bkt h) HBK)) MUs WM
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as TABh;
  clear TAB; rewrite <- EBA in TABh.
  zstep.
  remember (tab_of (d_hs D) (bkt h)) as hd eqn:Ehd.
  assert (Rhd : (0 <= hd <= Z.of_nat (length (d_hs D)))%Z) by (rewrite Ehd; apply tab_of_range).
  rewrite (sx32_small_A hd) by lia.
  do 7 zstep.
  assert (Ehd31 : Z.land hd 2147483647 = hd).
  { change 2147483647%Z with (Z.ones 31). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  rewrite Ehd31.
  destruct (unbox _ REP) as (_ & NU & M1 & ND & FS & TT & DT & SD & FF).
  let mm := curmem in
  pose proof (rw_cells_transport ctasegs _ m mm _ _ M1 MUs WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as M1m;
  pose proof (node_family_transport _ m mm _ _ _ ND MUs WM ltac:(cbn [disjoint_from]; lia) ltac:(unfold d_n; lia)) as NDm.
  eapply find_loop with (hs := d_hs D) (DNB := DNB) (k := S (length (d_hs D))).
  all: try (first [ exact HF | exact NDm | exact M1m | (rewrite Ehd; apply walk_start) | lia ]).
  (* [comment removed for export] *)
  { intros NF ax0 ax2.
    (* [comment removed for export] *)
    let mm := curmem in
    pose proof (rw_cells_transport ctasegs _ m mm _ _ NU MUs WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as NUm;
    pose proof (rw_cells_transport ctasegs _ m mm _ _ TT MUs WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as TTm;
    pose proof (rw_cells_transport ctasegs _ m mm _ _ DT MUs WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as DTm;
    pose proof (rw_cells_transport ctasegs _ m mm _ _ SD MUs WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as SDm;
    pose proof (stk_transport_disjoint ctasegs _ m mm _ _ FF MUs WM ltac:(cbn [disjoint_from]; lia)) as FFm;
    pose proof (stk_transport_disjoint ctasegs _ m mm _ _ FS MUs WM ltac:(cbn [disjoint_from]; lia)) as FSm.
    unfold d_n in NUm, FSm.
    clear MUs NU TT DT SD FF FS ND NDm.
    do 2 zstep.
    sp_facts.
    call (lock_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ BA hd lo).
    all: rewrite ?Esp in *; try lia; try eassumption.
    lazymatch goal with H : exists w, rw_cells ctasegs _ BA [C4 w] |- _ => destruct H as (wl & BAC) end.
    zstep. zstep. ifT.
    do 3 zstep.
    assert (AMO : amo_aligned AW (Z_to_bv 64 11878168) = true) by (vm_compute; reflexivity).
    amo_step AMO. amo32_fix_lit.
    rewrite (sx32_small_A (Z.of_nat (length (d_hs D)))) by lia.
    zstep. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
    do 2 zstep.
    assert (En32 : Z.land (Z.of_nat (length (d_hs D)) + 1) 4294967295 = (Z.of_nat (length (d_hs D)) + 1)%Z).
    { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
    rewrite En32.
    zstep. dIfF_s.
    do 2 zstep.
    assert (En16 : Z.shiftr (Z.of_nat (length (d_hs D)) + 1) 16 = 0%Z).
    { rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
    rewrite En16.
    do 4 zstep. ifF.
    do 3 zstep.
    assert (ENn : Z.shiftl (Z.land (Z.of_nat (length (d_hs D)) + 1) 65535) 4 = (16 * (Z.of_nat (length (d_hs D)) + 1))%Z).
    { change 65535%Z with (Z.ones 16). rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. lia. }
    rewrite ENn.
    remember (DNB + 16 * (Z.of_nat (length (d_hs D)) + 1))%Z as NA eqn:ENA.
    let mm := curmem in
    destruct (stk_carve_lo mm NA (DNB + 2 ^ 20) 16%nat FSm ltac:(lia)) as [FS2 (nj & NCB)]; clear FSm;
    apply node_cells_of_cb in NCB.
    do 5 zstep.
    sp_facts.
    call (nstore_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ NA h SSB (d_tot D) (bv_unsigned sp + -104)%Z TR lo
            ws rest _ _ _).
    all: rewrite ?Esp, ?Esp0, ?Esp1 in *; rewrite <- ?Esz; try lia; try eassumption.
    zstep. zstep. zstep. zstep. zstep. dIf_closed.
    do 12 zstep.
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned sp + -112)%Z |- _ => rename H into STK end.
    release_frame FR1 STK (bv_unsigned sp - 104)%Z.
    release_frame FR0 STK (bv_unsigned sp - 88)%Z.
    release_frame FR STK (bv_unsigned sp).
    zstep.
    unfold depot_put_post. rewrite (depot_put_miss D _ ltac:(rewrite <- Eh; exact NF)). cbn [fst snd].
    rewrite <- Eh, map_length, <- Esz. unfold d_n.
    finish.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside app]. intros; lia.
    - subst BA NA hd. rewrite <- Esz in *.
      lazymatch goal with |- depot_rep _ _ _ _ ?mm =>
        eapply (depot_rep_miss D BK DNB SSB lo h sz (bv_unsigned sp - 224)%Z (bv_unsigned sp) _ m mm OK (unbox _ REP)) end;
        try eassumption; try lia. }
  (* [comment removed for export] *)
  { intros NZ ax1 ax2.
    do 12 zstep.
    lazymatch goal with H : stk ctasegs _ lo (bv_unsigned sp + -112)%Z |- _ => rename H into STK end.
    release_frame FR1 STK (bv_unsigned sp - 104)%Z.
    release_frame FR0 STK (bv_unsigned sp - 88)%Z.
    release_frame FR STK (bv_unsigned sp).
    zstep.
    unfold depot_put_post. rewrite (depot_put_hit D _ ltac:(rewrite <- Eh; exact NZ)). cbn [fst snd]. rewrite <- Eh.
    finish.
    - eapply munch_weaken; [| exact MUs]. unfold sub_fp. cbn [outside app]. intros; lia.
    - lazymatch goal with |- depot_rep _ _ _ _ ?mm =>
        apply (depot_rep_frame D BK DNB SSB lo _ m mm (unbox _ REP) OK MUs WM); cbn [disjoint_from]; lia end. }
Qed.
