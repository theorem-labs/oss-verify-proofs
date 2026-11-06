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
From OSSVerify.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_glue_defs R_sec_defs F_memset R_setshadow R_poison R_secalloc_ps0 R_mmapordie R_secalloc R_secalloc_p2 R_secalloc_p3 R_secalloc_p4.
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

Lemma zero_split32 : forall (m : mem) A N, (32 <= N)%Z ->
  rw_cells ctasegs m A [CB (Z.to_nat N) (repeat (Z_to_bv 8 0) (Z.to_nat N))] ->
  rw_cells ctasegs m A [CB 32 (repeat (Z_to_bv 8 0) 32)]
  /\ rw_cells ctasegs m (A + 32) [CB (Z.to_nat (N - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (N - 32)))].
Proof.
  intros m A N N_ge32 zeros_all.
  assert (N_cut : Z.to_nat N = (32 + Z.to_nat (N - 32))%nat) by lia.
  rewrite N_cut, repeat_app in zeros_all.
  destruct zeros_all as [[wf_all bytes_all] wr_all].
  cbn [cells_bytes cbytes cells_size csize] in bytes_all, wr_all.
  rewrite app_nil_r in bytes_all. rewrite Nat.add_0_r in wr_all.
  assert (two_pieces : rw_cells ctasegs m A
            ([CB 32 (repeat (Z_to_bv 8 0) 32)] ++ [CB (Z.to_nat (N - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (N - 32)))])).
  { split; [split|].
    - cbn [app cells_wf cell_wf]. rewrite !repeat_length. exact (conj eq_refl (conj eq_refl I)).
    - cbn [app cells_bytes cbytes]. rewrite app_nil_r. exact bytes_all.
    - cbn [app cells_size csize]. rewrite Nat.add_0_r. exact wr_all. }
  apply sec_rw_app2 in two_pieces. destruct two_pieces as [low_part high_part].
  split; [exact low_part | exact high_part].
Qed.

(* [comment removed for export] *)
Definition sb_W (sp P SZ T PAB n : Z) : list (Z * Z) :=
  [(P, P + sa_msz SZ); (sp - 160, sp - 96); (shad P, shad P + 512); (shad (P + 4096 + SZ), shad (P + sa_msz SZ));
   (T + 2872, T + 2888); (i_sec_mutex, i_sec_mutex + 4); (PAB + 8 * n, PAB + 8 * n + 8); (i_sec_nres + 8, i_sec_nres + 16);
   (i_sec_sorted, i_sec_sorted + 40); (i_sec_bylog, i_sec_bylog + 512); (i_gstat_alloc, i_gstat_alloc + 16)]%Z.

(* [comment removed for export] *)
Definition sb_K (P SZ PAB nres n T : Z) (ws : list word) (mm md : word) (m : mem) : Prop :=
  shdr m P (sa_msz SZ) SZ n
  /\ rw_cells ctasegs m (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))]
  /\ rw_cells ctasegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
  /\ rw_cells ctasegs m (shad (P + 4096 + SZ))
       [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))]
  /\ rw_cells ctasegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))]
  /\ sec_core m PAB nres (n + 1)
  /\ sec_pad m
  /\ sec_junk m
  /\ u64arr ctasegs m PAB (upd ws (Z.to_nat n) (Z_to_bv 64 P)).

Lemma sb_common : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (mA : mem) (SZ P PAB nres n TCX T lo : Z) (ws : list word) (mm md : word) (shj1 shj2 : list byte)
    (Q : machine_state -> Prop),
  (65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2^47)%Z -> (P mod 4096 = 0)%Z ->
  gobj P (sa_msz SZ) lo -> gobj T 4096 lo -> gobj TCX 0xa0 lo -> gobj PAB 0x800000 lo ->
  sapart P (sa_msz SZ) T 4096 -> sapart P (sa_msz SZ) TCX 0xa0 -> sapart T 4096 TCX 0xa0 ->
  sapart P (sa_msz SZ) PAB 0x800000 -> sapart T 4096 PAB 0x800000 ->
  (0 <= n <= nres)%Z -> Z.of_nat (length ws) = nres -> (nres <= 2^20)%Z -> (nres mod 16384 = 0)%Z -> (n < 2^20)%Z ->
  sa_frame mA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  mod_frame mA (Z_to_bv 64 (bv_unsigned sp - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
    (Z_to_bv 64 (sa_msz SZ)) ->
  stk ctasegs mA lo (bv_unsigned sp - 144) -> mm_gcells mA -> sec_page mA ->
  ps_cells mA -> thread_cells TCX T mA -> rw_cells ctasegs mA (T + 2872) [C8 mm; C8 md] ->
  sec_core mA PAB nres n -> sec_pad mA -> sec_junk mA -> u64arr ctasegs mA PAB ws -> sec_range mA PAB ->
  rw_cells ctasegs mA (shad P) [CB 512 shj1] ->
  rw_cells ctasegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2] ->
  (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 160)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs mA ->
  (forall (m2 : mem) (ra2 t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' : word) (k : Z) (jf : list byte) (b : byte)
      (jj : list byte) (w1 w2 w3 w4 ga gm : word) (bl : list word),
    munch (sb_W (bv_unsigned sp) P SZ T PAB n) mA m2 -> wmono ctasegs mA m2 -> mem_inv ctasegs m2 ->
    stk ctasegs m2 lo (bv_unsigned sp - 96) ->
    rw_cells ctasegs m2 (bv_unsigned sp - 96) [CB 8 jf; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells ctasegs m2 i_sec_chunks [C8 (Z_to_bv 64 PAB)] ->
    rw_cells ctasegs m2 i_sec_nres [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 n)] ->
    rw_cells ctasegs m2 i_sec_sorted [C1 b; CB 7 jj; C8 w1; C8 w2; C8 w3; C8 w4] ->
    length bl = 64%nat -> u64arr ctasegs m2 i_sec_bylog bl -> rw_cells ctasegs m2 i_gstat_alloc [C8 ga; C8 gm] ->
    rw_cells ctasegs m2 i_sec_mutex [C4 (Z_to_bv 64 1)] ->
    u64arr ctasegs m2 PAB ws -> sec_range m2 PAB -> mm_gcells m2 ->
    rw_cells ctasegs m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)] ->
    rw_cells ctasegs m2 (P + 24) [C8 (Z_to_bv 64 0)] ->
    rw_cells ctasegs m2 (P + 32) [CB (Z.to_nat (sa_msz SZ - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (sa_msz SZ - 32)))] ->
    rw_cells ctasegs m2 (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)] ->
    rw_cells ctasegs m2 (shad (P + 4096 + SZ))
      [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)))] ->
    rw_cells ctasegs m2 (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm + 1)); C8 (Z_to_bv 64 (bv_unsigned md + sa_msz SZ))] ->
    (0 <= k < 64)%Z -> (2 ^ k <= sa_msz SZ < 2 ^ (k + 1))%Z ->
    evt ctasegs Q
      (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
               (Z_to_bv 64 (P + 4096)) a1' a2' (Z_to_bv 64 n) (Z_to_bv 64 nres) a5' a6' a7' (Z_to_bv 64 (sa_msz SZ))
               (Z_to_bv 64 (63 - k)) (Z_to_bv 64 P) (Z_to_bv 64 P) (Z_to_bv 64 (P + sa_msz SZ)) (Z_to_bv 64 (P + 4096 + SZ))
               (Z_to_bv 64 7) (Z_to_bv 64 (P + 4096)) s10 s11 t3' t4' t5' t6')
          F (Z_to_bv 64 0x1a0ab4) fc None m2 (seg_rom ctasegs))) ->
  evt ctasegs Q
    (nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6 (sa_msz SZ)
                   (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom ctasegs))
          (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])).
Proof.
  intros ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA
    SZ P PAB nres n TCX T lo ws mm md shj1 shj2 Q.
  intros sz_facts p_page obj_P obj_T obj_X obj_A part_PT part_PX part_TX part_PA part_TA
    n_le ws_len nres_le nres_mod n_lt frame_A frame_M stack_A gcells_A page_A pois_A thr_A stat_A
    core_A pad_A junk_A arr_A range_A shlo_A shhi_A lo_shad lo_sp sp_hi inv_A cont.
  destruct sz_facts as (sz_lo & sz_mod & sz_hi).
  pose proof (sa_msz_facts SZ ltac:(lia)) as (msz_span & msz_mod).
  assert (msz_id : roundup4k (sa_msz SZ) = sa_msz SZ) by (apply roundup4k_id; exact msz_mod).
  assert (p_mod8 : (P mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
  assert (msz_mod8 : (sa_msz SZ mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
  pose proof obj_P as (p_pos & p_top & p_mem & p_img).
  pose proof obj_T as (t_pos & t_top & t_mem & t_img).
  pose proof obj_X as (x_pos & x_top & x_mem & x_img).
  pose proof obj_A as (a_pos & a_top & a_mem & a_img).
  assert (shad_lo_P : (SHB <= shad P)%Z) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (shad_tail : (shad (P + 4096 + SZ) + (sa_msz SZ - 4096 - SZ) / 8 = shad (P + sa_msz SZ))%Z)
    by (unfold shad; Z.div_mod_to_equations; nia).
  assert (shad_lo_cap : (shad P + 512 <= shad (P + 4096 + SZ))%Z) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (shad_mid_le : (shad (P + 4096 + SZ) <= shad (P + sa_msz SZ))%Z) by (unfold shad; Z.div_mod_to_equations; lia).
  assert (shad_end : (shad (P + sa_msz SZ) <= kHighShadowEnd + 1)%Z)
    by (unfold shad, SHB, kHighShadowEnd in *; Z.div_mod_to_equations; lia).
  assert (shad_lo_top : (shad P + 512 <= lo)%Z) by (unfold shad, SHB in *; Z.div_mod_to_equations; lia).
  assert (shad_hi_top : (shad (P + 4096 + SZ) + (sa_msz SZ - 4096 - SZ) / 8 <= lo)%Z)
    by (unfold shad, SHB in *; Z.div_mod_to_equations; lia).
  assert (shad_top_lo : (shad (P + sa_msz SZ) <= lo)%Z) by lia.
  assert (shad_lo_hi : (SHB <= shad (P + 4096 + SZ))%Z) by lia.
  assert (shad_lo_end : (shad P + 512 <= kHighShadowEnd + 1)%Z) by lia.
  destruct frame_A as (jf & frame_A).
  destruct thr_A as ((tsd_init & tsd_key & tsd_ptr & tsd_main) & tcx_cell).
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in tsd_init, tsd_key, tsd_ptr, tsd_main.
  destruct pois_A as (ps_cf & (ps_m2s1 & ps_m2s2 & ps_m2s3) & (ps_ss1 & ps_ss2) & ps_can & ps_thr).
  unfold g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold in ps_cf, ps_can, ps_thr.
  unfold g_got_real_memset, g_real_memset in ps_ss1, ps_ss2.
  destruct core_A as (chunks_A & nres_A & mutex_A).
  destruct junk_A as ((b & jj & w1 & w2 & w3 & w4 & sorted_A) & (bl & bl_len & bylog_A) & (ga & gm & gstat_A)).
  unfold sec_range in range_A. unfold sec_page in page_A. unfold sec_pad in pad_A.
  pose proof (munch_refl (sb_W (bv_unsigned sp) P SZ T PAB n) mA) as foot.
  pose proof (wmono_refl ctasegs mA) as mono.
  unfold sb_W, i_sec_mutex, i_sec_nres, i_sec_sorted, i_sec_bylog, i_gstat_alloc, INST, g_instance in foot.
  change i_sec_chunks with 6744608%Z in chunks_A. change i_sec_nres with 6744648%Z in nres_A.
  change i_sec_mutex with 6745216%Z in mutex_A. change (i_sec_mutex + 1)%Z with 6745217%Z in pad_A.
  change i_sec_sorted with 6744664%Z in sorted_A. change i_sec_bylog with 6744704%Z in bylog_A.
  change i_gstat_alloc with 6745240%Z in gstat_A. change i_sec_range with 6744616%Z in range_A.
  change i_sec_page with 6744600%Z in page_A.
  unfold gobj, sapart, img_hull_lo, img_hull_hi, kHighShadowEnd, SHB in *.
  hide_disj.
  eapply evt_cut.
  { eapply (mod_B_spec (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned sp - 96)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6
              (Z_to_bv 64 SZ) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6 F fc mA
              (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC) (Z_to_bv 64 (sa_msz SZ)) P (sa_msz SZ) (Z_to_bv 64 sec_name) lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 96)), ?msz_id by lia.
    - lia.
    - lia.
    - lia.
    - unfold hide; unfold img_hull_lo, img_hull_hi; exact p_img.
    - exact frame_M.
    - exact gcells_A.
    - replace (bv_unsigned sp - 96 - 48)%Z with (bv_unsigned sp - 144)%Z by lia. exact stack_A.
    - unfold kHighShadowEnd; lia.
    - lia.
    - lia.
    - exact inv_A. }
  intros ms1 post_M.
  destruct post_M as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> &
                      foot_M & mono_M & inv_1 & zeros_1 & stack_1 & gcells_1).
  rewrite msz_id in foot_M, zeros_1.
  rewrite ?(unsigned_lit (bv_unsigned sp - 96)) in foot_M, stack_1 by lia.
  destruct gcells_1 as (gc1 & gc2 & gc3 & gc4 & gc5).
  (* the shadow of the object is separated from the object itself, in either half of the address space *)
  assert (sep_lo : (shad P + 512 <= P \/ P + sa_msz SZ <= shad P)%Z).
  { unfold hide in p_mem. unfold shad, SHB in *. destruct p_mem as [low | high]; [right | left];
      Z.div_mod_to_equations; lia. }
  assert (sep_hi : (shad (P + 4096 + SZ) + (sa_msz SZ - 4096 - SZ) / 8 <= P \/ P + sa_msz SZ <= shad (P + 4096 + SZ))%Z).
  { unfold hide in p_mem. unfold shad, SHB in *. destruct p_mem as [low | high]; [right | left];
      Z.div_mod_to_equations; lia. }
  apply box in shlo_A. apply box in shhi_A.
  transport_after_call ctasegs mA m1 foot_M mono_M.
  pose proof (rw_cells_transport ctasegs _ mA m1 _ _ (unbox _ shlo_A) foot_M mono_M
                ltac:(cbn [disjoint_from cells_size csize Nat.add];
                      split; [lia | split; [lia | exact I]])) as shlo_1.
  pose proof (rw_cells_transport ctasegs _ mA m1 _ _ (unbox _ shhi_A) foot_M mono_M
                ltac:(cbn [disjoint_from cells_size csize Nat.add];
                      split; [lia | split; [lia | exact I]])) as shhi_1.
  clear shlo_A shhi_A foot_M mono_M inv_A frame_M gcells_A.
  unfold sa_retA. rewrite (ret_pc_even 0x1a0910) by lia.
  (* the mmap returns the zeroed object at P; carve its header off the body *)
  destruct (zero_split32 m1 P (sa_msz SZ) ltac:(lia) zeros_1) as (hdr_zero & body_zero). clear zeros_1.
  (* 0x1a0910 .. 0x1a0a0c: poison both shadow ends, count the mapping, write the header, take the mutex *)
  apply (sa_p2 (Z_to_bv 64 (bv_unsigned sp - 96)) gp s4 s6 s7 s9 s10 s11 F fc m1 P SZ TCX T nres n lo mm md shj1 shj2 Q).
  - split; [lia | split; [exact sz_mod | exact sz_hi]].
  - exact p_page.
  - exact obj_P.
  - exact obj_T.
  - exact obj_X.
  - exact part_PT.
  - exact part_PX.
  - exact part_TX.
  - lia.
  - unfold sec_page. change i_sec_page with 6744600%Z. exact page_A.
  - unfold ps_cells, m2s_cells, setshadow_cells, g_got_common_flags, g_can_poison,
      g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset.
    refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption.
  - unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
    refine (conj (conj _ (conj _ (conj _ _))) _); assumption.
  - exact stat_A.
  - exact hdr_zero.
  - exact shlo_1.
  - exact shhi_1.
  - change i_sec_mutex with 6745216%Z. exact mutex_A.
  - unfold sec_pad. change (i_sec_mutex + 1)%Z with 6745217%Z. exact pad_A.
  - change i_sec_nres with 6744648%Z. exact nres_A.
  - rewrite (unsigned_lit (bv_unsigned sp - 96)) by lia. exact stack_1.
  - unfold kHighShadowEnd. lia.
  - rewrite (unsigned_lit (bv_unsigned sp - 96)) by lia. lia.
  - rewrite (unsigned_lit (bv_unsigned sp - 96)) by lia. lia.
  - exact inv_1.
  - intros m2 ra2 t0' t1' t2' a1' a2' a4' a5' a6' a7' t3' t4' t5' t6'
      foot_2 mono_2 inv_2 hdr_2 shlo_2 shhi_2 stat_2 mutex_2 stack_2.
    rewrite (unsigned_lit (bv_unsigned sp - 96)) in foot_2, stack_2 by lia.
    unfold sa_W2, i_sec_mutex, INST, g_instance in foot_2.
    transport_after_call ctasegs m1 m2 foot_2 mono_2.
    clear foot_2 mono_2.
    assert (hdr3 : rw_cells ctasegs m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)])
      by exact (proj1 (proj1 (sec_rw_app2 m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)]
                                           [C8 (Z_to_bv 64 0)]) hdr_2)).
    assert (idx0 : rw_cells ctasegs m2 (P + 24) [C8 (Z_to_bv 64 0)])
      by exact (proj2 (proj1 (sec_rw_app2 m2 P [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (sa_msz SZ)); C8 (Z_to_bv 64 SZ)]
                                           [C8 (Z_to_bv 64 0)]) hdr_2)).
    clear hdr_2.
    (* 0x1a0a0c .. 0x1a0ab4: s3 gets 63 - log2 of the mapped size, the count of its leading zero bits *)
    pose proof (Z.log2_spec (sa_msz SZ) ltac:(lia)) as (log_lo & log_hi).
    assert (log_rng : (0 <= Z.log2 (sa_msz SZ) < 64)%Z)
      by (split; [apply Z.log2_nonneg | apply Z.log2_lt_pow2; lia]).
    change SEC with 6744600%Z.
    eapply (clz_block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ _ (Z.log2 (sa_msz SZ)) nres Q).
    + exact (proj1 (proj1 (sec_rw_app2 m2 6744648 [C8 (Z_to_bv 64 nres)] [C8 (Z_to_bv 64 n)]) nres_A)).
    + exact log_rng.
    + rewrite (unsigned_lit (sa_msz SZ)) by lia. split; [exact log_lo | exact log_hi].
    + intros a1'' a2'' a5'' a6''.
      assert (gcells_now : mm_gcells m2)
        by (unfold mm_gcells; refine (conj _ (conj _ (conj _ (conj _ _)))); assumption).
      assert (range_now : sec_range m2 PAB)
        by (unfold sec_range; change i_sec_range with 6744616%Z; exact range_A).
      change 6744600%Z with SEC.
      apply (cont m2 ra2 t0' t1' t2' a1'' a2'' a5'' a6'' a7' t3' t4' t5' t6' (Z.log2 (sa_msz SZ))
                  jf b jj w1 w2 w3 w4 ga gm bl); try eassumption; try lia.
Qed.
