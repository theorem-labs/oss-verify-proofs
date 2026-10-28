(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Lemma x4k_cells_bytes_c8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof. induction ws as [|w ws IH]; cbn [map cells_bytes u64s cbytes]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma x4k_cells_size_c8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; cbn [map cells_size csize length]; lia. Qed.

Lemma x4k_cells_wf_c8 : forall ws, cells_wf (map C8 ws).
Proof. induction ws as [|w ws IH]; cbn [map cells_wf cell_wf]; tauto. Qed.

Lemma x4k_u64arr_c8 : forall segs m A ws, u64arr segs m A ws -> rw_cells segs m A (map C8 ws).
Proof.
  intros segs m A ws [HB HW]. split; [split|].
  - apply x4k_cells_wf_c8.
  - rewrite x4k_cells_bytes_c8. exact HB.
  - rewrite x4k_cells_size_c8. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact HW.
Qed.

Lemma x4k_c8_u64arr : forall segs m A ws, rw_cells segs m A (map C8 ws) -> u64arr segs m A ws.
Proof.
  intros segs m A ws [[_ HB] HW]. split.
  - rewrite <- x4k_cells_bytes_c8. exact HB.
  - rewrite x4k_cells_size_c8 in HW. replace (8 * Z.of_nat (length ws)) with (Z.of_nat (8 * length ws)) by lia. exact HW.
Qed.

Lemma x4k_u64s_slice : forall ws j, (j < length ws)%nat ->
  firstn 8 (skipn (8 * j) (u64s ws)) = le8 (nth j ws (Z_to_bv 64 0)).
Proof.
  induction ws as [|w ws IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; cbn [u64s nth].
  - rewrite Nat.mul_0_r, skipn_O, firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    apply firstn_all2. rewrite length_le8. lia.
  - rewrite skipn_app, length_le8, skipn_all2 by (rewrite length_le8; lia). cbn [app].
    replace (8 * S j - 8)%nat with (8 * j)%nat by lia. apply IH. lia.
Qed.

Section WordZ.
Variable segs : list Segment.
Variable zv : list Z.
Variable xs : list word.
Variable m : word -> option byte.
Local Notation E := (kE zv xs).
Local Notation na := (length zv).

Lemma x4k_word_ok : forall a v b c A ws j,
  zatoms_lt na a = true -> zatoms_lt na v = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> zden zv a + 8 <= 2^64 ->
  bytes_at segs m A (u64s ws) -> (j < length ws)%nat -> zden zv a = A + 8 * Z.of_nat j ->
  nth j ws (Z_to_bv 64 0) = Z_to_bv 64 (zden zv v) ->
  kentry_ok segs E m (zk_ent (ZKWord a 8 v)).
Proof.
  intros a v b c A ws j Ha Hv Hs H1 H2 H3 HB Hj HA HV.
  assert (ES : estart E (zsa a) = zden zv a)
    by (first [ apply (estart_zsa_split segs zv xs m a b c) | apply (estart_zsa_split zv xs a b c) ]; assumption).
  assert (FL : flat E (zsa a) (Z.of_nat 8)) by (unfold flat; rewrite ES; lia).
  cbn [zk_ent kentry_ok]. split; [lia|]. split; [exact FL|].
  assert (AD : adenot E (zsa a) = wa (A + Z.of_nat (8 * j))).
  { apply bv_eq. rewrite (flat_u E (zsa a) (Z.of_nat 8) FL), ES, wa_unsigned by lia. lia. }
  rewrite AD, (zle_ok zv xs v Hv), <- HV.
  assert (R2 : rdn segs m (wa (A + Z.of_nat (8 * j))) 8 = Some (firstn 8 (skipn (8 * j) (u64s ws))))
    by (apply bytes_at_rdn; [exact HB | rewrite u64s_length; lia]).
  rewrite x4k_u64s_slice in R2 by exact Hj.
  exact R2.
Qed.
End WordZ.

Ltac x4k_word_try segs zv xs m a v b c A ws H j :=
  first [ apply (x4k_word_ok segs zv xs m a v b c A ws j);
          [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | kx_arith | kx_arith | kx_arith | exact H | cbn [length]; lia
          | cbv [zden nth]; lia | cbv [zden nth]; first [reflexivity | f_equal; lia] ]
        | lazymatch j with
          | 14%nat => fail
          | _ => x4k_word_try segs zv xs m a v b c A ws H (S j)
          end ].

Ltac x4k_know1 segs zv xs m :=
  lazymatch goal with
  | |- kentry_ok _ _ _ (zk_ent (ZKWord ?a 8 ?v)) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        match goal with H : bytes_at segs m ?A (u64s ?ws) |- _ =>
          x4k_word_try segs zv xs m a v b c A ws H O end
      end
  | |- kentry_ok _ _ _ (zk_ent (ZKWr ?a ?n)) =>
      let s1 := eval vm_compute in (zsa a) in
      lazymatch s1 with SA ?b ?c =>
        first [ match goal with H : wr_at segs m ?A ?N |- _ =>
                  apply (zk_wr_ok segs zv xs m a n b c A N);
                  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                  | kx_arith | kx_arith | kx_arith | exact H | cbv [zden nth]; lia | cbv [zden nth]; lia ] end
              | match goal with H : u8arr segs m ?A ?bs |- _ =>
                  apply (zk_wr_ok segs zv xs m a n b c A (Z.of_nat (length bs)));
                  [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                  | kx_arith | kx_arith | kx_arith | exact (proj2 H) | cbv [zden nth]; lia | cbv [zden nth]; lia ] end ]
      end
  | |- _ => kx_know1 segs zv xs m
  end.

Ltac kx_god DIRS :=
  lazymatch goal with
  | |- kx_pending ?segs ?Q ?F ?fc ?m ?rom ?pc ?stops ?fuel ?xl ?zv ?zs ?zks ?zrs =>
    let na := eval vm_compute in (length zv) in
    let sr := constr:(ELit 0 :: map (fun z => lnorm (zx z)) zs) in
    let kn0 := constr:(map zk_ent zks) in
    let r0 := eval vm_compute in (sym_exec segs fuel true stops (SCR DIRS [] []) (SS pc sr [] (kn0 ++ atom_ranges na) na) []) in
    let reads0 := eval vm_compute in (kx_reads_of na (snd (fst r0))) in
    let ispec := eval vm_compute in (find_idx zks) in
    let ifs := lazymatch ispec with
               | Some (?ztl, ?zT) =>
                   let s0 := eval vm_compute in (zle (ZSub (ZL 64) ztl)) in
                   let Tx := eval vm_compute in (zle zT) in
                   eval vm_compute in (idx_facts Tx s0 (snd (fst r0)))
               | None => constr:(@nil kentry)
               end in
    let kn1 := constr:((kn0 ++ atom_ranges na) ++ (read_ranges na reads0 ++ ifs)) in
    let tsv := eval vm_compute in (tabs_of zks) in
    let tfs := lazymatch tsv with
               | nil => constr:(@nil kentry)
               | _ => eval vm_compute in (tab_ranges kn1 (tabs_of zks) na reads0)
               end in
    let shv := eval vm_compute in (shz_of zks) in
    let sfs := lazymatch shv with
               | nil => constr:(@nil kentry)
               | _ => eval vm_compute in (shz_ranges kn1 (shz_of zks) na reads0)
               end in
    let kn := lazymatch constr:((tsv, shv)) with
              | (nil, nil) => kn1
              | _ => constr:((kn0 ++ atom_ranges na) ++ ((tfs ++ sfs) ++ (read_ranges na reads0 ++ ifs)))
              end in
    let r := eval vm_compute in (sym_exec segs fuel true stops (SCR DIRS [] []) (SS pc sr [] kn na) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let reads := eval vm_compute in (kx_reads_of na scs) in
      let ws := constr:(map (Z_to_bv 64) zv) in
      let KXS := fresh "KXxs" in
      pose (KXS := kx_vals segs m ws reads);
      let xs := constr:(KXS) in
      let KXE := fresh "KXE" in
      pose (KXE := kx_env ws xs);
      let E := constr:(KXE) in
      let KXA := fresh "KXA" in
      assert (KXA : forall j, (j < length zv)%nat -> ev KXE j = Z_to_bv 64 (nth j zv 0)) by exact (kE_atom zv KXS);
      let rr := constr:(map zr_reg zrs) in
      let HK := fresh "HK" in let HRR := fresh "HRR" in let HK1 := fresh "HK1" in let HSH := fresh "HSH" in
      assert (HSH : Forall (shz_ok m E) (shz_of zks)) by (cbn [shz_of]; kx_forall; kx_shz1 segs zv xs m);
      assert (HK1 : know_ok segs E m kn1);
      [ unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [ | apply atom_ranges_ok] | apply Forall_app; split ];
        [ apply Forall_map_iff; kx_forall; x4k_know1 segs zv xs m
        | apply (read_ranges_ok segs m ws reads); [ vm_compute; reflexivity | | vm_compute; lia ];
          intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth
        | lazymatch ispec with
          | Some (?ztl, ?zT) =>
              let s0 := eval vm_compute in (zle (ZSub (ZL 64) ztl)) in
              let Tx := eval vm_compute in (zle zT) in
              let tlz := eval cbv [zden nth] in (zden zv ztl) in
              apply (idx_facts_ok segs E m Tx s0 tlz (snd (fst r0)));
              [ exact (zle_ok zv xs zT (eq_refl true)) | exact (zle_ok zv xs (ZSub (ZL 64) ztl) (eq_refl true)) | lia ]
          | None => constructor
          end ]
      | assert (HK : know_ok segs E m kn);
      [ lazymatch constr:((tsv, shv)) with
        | (nil, nil) => exact HK1
        | _ => let HKA := fresh "HKA" in let HKB := fresh "HKB" in
               pose proof (proj1 (Forall_app _ _ _) HK1) as [HKA HKB];
               unfold know_ok; apply Forall_app; split; [exact HKA|]; apply Forall_app; split; [| exact HKB];
               apply Forall_app; split;
               [ lazymatch tsv with
                 | nil => constructor
                 | _ => let TEQ := fresh "TEQ" in
                        assert (TEQ : tab_ranges kn1 (tabs_of zks) na reads0 = tfs) by (vm_compute; reflexivity);
                        rewrite <- TEQ; clear TEQ;
                        apply (tab_ranges_ok segs m ws reads kn1 (tabs_of zks));
                        [ vm_compute; reflexivity | exact HK1 | cbn [tabs_of]; kx_forall; kx_tab1 segs zv xs m
                        | intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth | vm_compute; lia ]
                 end
               | lazymatch shv with
                 | nil => constructor
                 | _ => let SEQ := fresh "SEQ" in
                        assert (SEQ : shz_ranges kn1 (shz_of zks) na reads0 = sfs) by (vm_compute; reflexivity);
                        rewrite <- SEQ; clear SEQ;
                        apply (shz_ranges_ok segs m ws reads kn1 (shz_of zks));
                        [ vm_compute; reflexivity | exact HK1 | exact HSH
                        | intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth | vm_compute; lia ]
                 end ]
        end
      | clear HK1;
        assert (HRR : Forall (region_ok segs m E) rr);
        [ apply Forall_map_iff; kx_forall; kx_region1 segs zv xs m
        | let KXR := fresh "KXR" in
          assert (KXR : regs_ok E sr (mkRl xl)) by kx_regs_ok zv;
          unfold kx_pending;
          refine (kx_run_evt segs fuel stops (SCR DIRS [] []) pc sr kn na ss' scs scr' E (mkRl xl) F fc m rom Q
                    (rfull_mkRl xl) _ KXR HK _ _);
          [ vm_cast_no_check (@eq_refl (sym_state * list sidecond * scripts) r)
          | apply (kx_scs_bulk2 segs m ws reads kn rr (shz_of zks) scs); [ vm_compute; reflexivity | exact HK | exact HRR | exact HSH | ];
            let rest := eval vm_compute in (List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs) in
            let REQ := fresh "REQ" in
            assert (REQ : List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs = rest) by (vm_compute; reflexivity);
            change (length ws) with na; rewrite REQ; clear REQ; change (scs_denot segs m E rest); unfold scs_denot; kx_forall;
            kx_sc_rest segs m ws reads na
          | clear HRR HSH; intros KXLF; cbn [s_log s_regs s_pc] in KXLF |- * ] ] ] ]
    end
  end.

Tactic Notation "kx_rund" uconstr(STOPS) uconstr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(DIRS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in
  let D := constr:(DIRS : list bool) in
  kx_prep S Fu K R; kx_god D.
