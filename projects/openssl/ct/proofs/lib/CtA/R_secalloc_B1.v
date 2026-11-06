(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk SysStep ITree StoreFast. 
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.openssl.ct.lib.A Require Import Shadow R_secalloc_math.
From OSSVerify.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4 R_secalloc_B0 R_mmapfixed R_mapordie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
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
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= clear_big; lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac hide_disj := repeat match goal with
  | H : (?A \/ ?B) |- _ => change (hide (A \/ B)) in H
  end.
(* [comment removed for export] *)
Ltac lia_p := zify_prune_plain; Zify.zify; xlia zchecker.
Ltac disj_one :=
  first [ lia_p
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].
Ltac my_disj := repeat match goal with |- _ /\ _ => split end; try exact I; disj_one.
Local Ltac tslia ::= first [ exact I | clear_big; my_disj ].
(* [comment removed for export] *)
Local Ltac disj_try H := let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; decompose [or] H'; lia_p.
Module RS.
  Import Ltac2.
  Ltac2 is_hdisj (t : constr) : bool := lazy_match! t with hide (_ \/ _) => true | _ => false end.
  Ltac2 rsearch () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if is_hdisj ty then (if SF2.meets (SF2.vars_of [] ty) gv then Some id else None) else None
                 end) (Control.hyps ()) in
    let rec go l := match l with
      | [] => Control.zero (Tactic_failure None)
      | id :: l' => Control.plus (fun () => ltac1:(h |- disj_try h) (Ltac1.of_constr (Control.hyp id))) (fun _ => go l')
      end in
    go ids.
  Ltac2 rsearch1 () : unit := Control.enter rsearch.
End RS.
Local Ltac disj_rel := ltac2:(RS.rsearch1 ()).
Local Ltac disj_one ::=
  first [ lia_p
        | disj_rel
        | match goal with H : hide (_ \/ _) |- _ =>
            let H' := fresh "Hd" in pose proof H as H'; unfold hide in H'; destruct H' as [H'|H']; lia_p
          end ].

(* [comment removed for export] *)
Definition sb1_W (sp P SZ T PAB n : Z) : list (Z * Z) := ((sp - 464, sp - 96) :: sb_W sp P SZ T PAB n)%Z.

(* [comment removed for export] *)
Definition sb1_mid (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (P SZ PAB nres T : Z) (ws : list word) (mm md : word)
    (m : mem) : Prop :=
  exists (jf : list byte) (b : byte) (jj : list byte) (w1 w2 w3 w4 ga gm : word) (bl : list word),
    rw_cells ctasegs m (bv_unsigned sp - 96)
      [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells ctasegs m i_sec_chunks [C8 (Z_to_bv 64 PAB)]
    /\ rw_cells ctasegs m i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nres)]
    /\ rw_cells ctasegs m i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4]
    /\ length bl = 64%nat /\ u64arr ctasegs m i_sec_bylog bl
    /\ rw_cells ctasegs m i_gstat_alloc [C8 ga; C8 gm]
    /\ rw_cells ctasegs m i_sec_mutex [C4 (Z_to_bv 64 1)]
    /\ u64arr ctasegs m PAB ws
    /\ sec_range m PAB
    /\ rw_cells ctasegs m P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)]
    /\ rw_cells ctasegs m (P + 24) [C8 (Z_to_bv 64 0)]
    /\ rw_cells ctasegs m (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))]
    /\ rw_cells ctasegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
    /\ rw_cells ctasegs m (shad (P + 4096 + SZ))
         [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))]
    /\ rw_cells ctasegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))].

Definition secalloc_B1_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P SZ PAB nres T lo : Z) (ws : list word) (mm md : word) (mA : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (kk : Z) (mB : mem),
    ms' = MSsvc (mfi0_regs (Z_to_bv 64 0x1a0cb0) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0' t1' t2' a6'
                   (PAB + 8 * nres) 0x20000 (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ))
                   (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None mB (seg_rom ctasegs)
    /\ munch (sb1_W (bv_unsigned sp) P SZ T PAB nres) mA mB /\ wmono ctasegs mA mB /\ mem_inv ctasegs mB
    /\ mfi_frame mB (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 0x1a0cb0) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
         (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - kk)) (Z_to_bv 64 (P + 4096))
    /\ stk ctasegs mB lo (bv_unsigned sp - 192)
    /\ mm_gcells mB
    /\ (0 <= kk < 64)%Z /\ (2 ^ kk <= sa_msz SZ < 2 ^ (kk + 1))%Z
    /\ sb1_mid sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 P SZ PAB nres T ws mm md mB.

Lemma secalloc_B1_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mA : mem) (SZ P PAB nres TCX T lo : Z) (ws : list word) (mm md : word) (shj1 shj2 : list byte),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) TCX 0xa0 -> sapart T 4096 TCX 0xa0 ->
  sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  (0 <= nres)%Z -> Z.of_nat (length ws) = nres -> (nres + 16384 <= 2^20)%Z -> (nres mod 16384 = 0)%Z -> (PAB mod 4096 = 0)%Z ->
  sa_frame mA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  mod_frame mA (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) ->
  stk ctasegs mA lo (bv_unsigned sp - 144) -> mm_gcells mA -> sec_page mA ->
  ps_cells mA -> thread_cells TCX T mA -> rw_cells ctasegs mA (T + 2872) [C8 mm; C8 md] ->
  sec_core mA PAB nres nres -> sec_pad mA -> sec_junk mA -> u64arr ctasegs mA PAB ws -> sec_range mA PAB ->
  rw_cells ctasegs mA (shad P) [CB 512 shj1] ->
  rw_cells ctasegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2] ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs mA ->
  evt ctasegs (secalloc_B1_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P SZ PAB nres T lo ws mm md mA)
    (nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom ctasegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])).
Proof.
  intros ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA SZ P PAB nres TCX T lo ws mm md
    shj1 shj2 size_ok p_al obj_p obj_t obj_x obj_ab apart_pt apart_px apart_tx apart_pab apart_tab nres_pos ws_len
    nres_room nres_al pab_al frame_sa frame_mod stack_a gcells_a page_a poison_a thread_a tstat_a core_a pad_a junk_a
    chunks_a range_a shlo_a shhi_a lo_shadow lo_sp sp_top inv_a.
  apply (sb_common ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA SZ P PAB nres nres TCX T
           lo ws mm md shj1 shj2 _ size_ok p_al obj_p obj_t obj_x obj_ab apart_pt apart_px apart_tx apart_pab apart_tab
           ltac:(lia) ws_len ltac:(lia) nres_al ltac:(lia) frame_sa frame_mod stack_a gcells_a page_a poison_a thread_a
           tstat_a core_a pad_a junk_a chunks_a range_a shlo_a shhi_a lo_shadow ltac:(lia) sp_top inv_a).
  intros m2 ra2 t0b t1b t2b a1b a2b a5b a6b a7b t3b t4b t5b t6b k jf b jj w1 w2 w3 w4 ga gm bl
    win2 grow2 inv2 stack2 frame2 chunks2 counts2 sorted2 bl_len bylog2 gstat2 lock2 arr2 range2 gcells2 hdr2 hdr24
    zeros2 shlo2 shhi2 tstat2 k_rng k_log.
  clear frame_sa frame_mod stack_a gcells_a page_a poison_a thread_a tstat_a core_a pad_a junk_a chunks_a range_a
    shlo_a shhi_a inv_a.
  unfold kHighShadowEnd in lo_shadow.
  pose proof (sa_msz_facts SZ ltac:(lia)) as (msz_rng & msz_al).
  pose proof (sa_shad_facts P SZ lo p_al ltac:(lia) ltac:(lia) obj_p ltac:(lia))
    as (shad_base & _ & shad_split & _ & _ & _ & shad_tail & shad_cap & _).
  destruct obj_ab as (ab_pos & ab_top & _ & _). destruct obj_t as (t_pos & t_top & _ & _).
  destruct obj_p as (p_pos & p_top & _ & _).
  unfold sec_range, i_sec_range in range2. change (INST + 0x50)%Z with 6744616%Z in range2.
  change SEC with 6744600%Z.
  zstep. ifT.
  do 9 zstep.
  replace (nres ≪ 3 + PAB)%Z with (PAB + 8 * nres)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (sp_low : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 96)) = (bv_unsigned sp - 96)%Z) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (mapordie_A_spec (Z_to_bv 64 1707184) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0b t1b t2b
              (Z_to_bv 64 GSTAT) (Z_to_bv 64 6744600) (Z_to_bv 64 6744616) (Z_to_bv 64 6744616) a5b a6b a7b
              (Z_to_bv 64 (sa_msz SZ)) (Z_to_bv 64 (63 - k)) (Z_to_bv 64 (P + 4096)) (Z_to_bv 64 P)
              (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ)) (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11
              t3b t4b t5b t6b F fc m2 (PAB + 8 * nres) 131072 lo); rewrite ?sp_low.
    - lia.
    - lia.
    - lia.
    - reflexivity.
    - lia.
    - exact gcells2.
    - exact stack2.
    - unfold kHighShadowEnd. lia.
    - lia.
    - lia.
    - exact inv2. }
  intros ms' (t0c & t1c & t2c & a6c & t3c & t4c & t5c & t6c & mB & -> & win3 & grow3 & inv3 & frame3 & stack3 & gcells3).
  rewrite sp_low in win3, stack3.
  assert (win_all : munch (sb1_W (bv_unsigned sp) P SZ T PAB nres) mA mB).
  { apply (munch_trans _ mA m2 mB).
    - refine (munch_weaken _ _ mA m2 _ win2).
      intros x out_x. unfold sb1_W in out_x. cbn [outside] in out_x. exact (proj2 out_x).
    - refine (munch_weaken _ _ m2 mB _ win3).
      intros x out_x. unfold sb1_W in out_x. cbn [outside] in out_x |- *. split; [lia | exact I]. }
  assert (stackB : stk ctasegs mB lo (bv_unsigned sp - 192)).
  { replace (bv_unsigned sp - 192)%Z with (bv_unsigned sp - 96 - 96)%Z by lia. exact stack3. }
  assert (carry : forall A cs, rw_cells ctasegs m2 A cs ->
            (A + Z.of_nat (cells_size cs) <= bv_unsigned sp - 464 \/ bv_unsigned sp - 96 <= A)%Z ->
            rw_cells ctasegs mB A cs).
  { intros A cs held apart. apply (rw_cells_transport ctasegs _ m2 mB A cs held win3 grow3).
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (carry64 : forall A xs, u64arr ctasegs m2 A xs ->
            (A + 8 * Z.of_nat (length xs) <= bv_unsigned sp - 464)%Z -> u64arr ctasegs mB A xs).
  { intros A xs held apart. apply (u64arr_transport ctasegs _ m2 mB A xs held win3 grow3).
    cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (carry _ _ frame2 ltac:(right; lia)) as frameB.
  pose proof (carry _ _ tstat2 ltac:(cbn [cells_size csize Nat.add]; lia)) as tstatB.
  pose proof (carry _ _ hdr2 ltac:(cbn [cells_size csize Nat.add]; lia)) as hdrB.
  pose proof (carry _ _ hdr24 ltac:(cbn [cells_size csize Nat.add]; lia)) as hdr24B.
  pose proof (carry _ _ zeros2 ltac:(cbn [cells_size csize Nat.add]; lia)) as zerosB.
  pose proof (carry _ _ shlo2 ltac:(cbn [cells_size csize Nat.add]; lia)) as shloB.
  pose proof (carry _ _ shhi2 ltac:(cbn [cells_size csize Nat.add]; lia)) as shhiB.
  pose proof (carry64 _ _ arr2 ltac:(lia)) as arrB.
  unfold i_sec_chunks, i_sec_nres, i_sec_mutex, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance
    in chunks2, counts2, lock2, sorted2, bylog2, gstat2.
  pose proof (carry _ _ chunks2 ltac:(cbn [cells_size csize Nat.add]; lia)) as chunksB.
  pose proof (carry _ _ counts2 ltac:(cbn [cells_size csize Nat.add]; lia)) as countsB.
  pose proof (carry _ _ lock2 ltac:(cbn [cells_size csize Nat.add]; lia)) as lockB.
  pose proof (carry _ _ sorted2 ltac:(cbn [cells_size csize Nat.add]; lia)) as sortedB.
  pose proof (carry _ _ gstat2 ltac:(cbn [cells_size csize Nat.add]; lia)) as gstatB.
  pose proof (carry64 _ _ bylog2 ltac:(rewrite bl_len; lia)) as bylogB.
  pose proof (carry _ _ range2 ltac:(cbn [cells_size csize Nat.add]; lia)) as rangeB.
  apply evt_done. red.
  exists t0c, t1c, t2c, a6c, t3c, t4c, t5c, t6c, k, mB.
  refine (conj eq_refl (conj win_all (conj (wmono_trans ctasegs _ _ _ grow2 grow3)
            (conj inv3 (conj frame3 (conj stackB (conj gcells3 (conj k_rng (conj k_log _))))))))).
  exists jf, b, jj, w1, w2, w3, w4, ga, gm, bl.
  exact (conj frameB (conj chunksB (conj countsB (conj sortedB (conj bl_len (conj bylogB (conj gstatB (conj lockB
           (conj arrB (conj rangeB (conj hdrB (conj hdr24B (conj zerosB (conj shloB (conj shhiB tstatB))))))))))))))).
Qed.
