(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Exec MState Frame Mem Cells Step.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RGS.
Import RGM.

#[local] Notation W z := (Z_to_bv 64 z) (only parsing).
#[local] Notation C8 := Cells.C8 (only parsing).
#[local] Notation C4 := Cells.C4 (only parsing).
#[local] Notation C1 := Cells.C1 (only parsing).

Section Stmt.
Variable segs : list Segment.
Variable T : ctab.
#[local] Notation ro_cells := (Step.ro_cells segs) (only parsing).
#[local] Notation rw_cells := (Step.rw_cells segs) (only parsing).
#[local] Notation stk := (Frame.stk segs) (only parsing).
#[local] Notation y := (c_lay T) (only parsing).

(* [comment removed for export] *)
Definition dflt : desc := D 0 0 0 0 0.

(* [comment removed for export] *)
Definition desc_at (m : word -> option byte) (g : Z) (d : desc) : Prop :=
  ro_cells m g [C8 (W (d_beg d)); C8 (W (d_size d)); C8 (W (d_swr d))]
  /\ ro_cells m (g + 40) [C8 (W (d_dyn d))]
  /\ ro_cells m (g + 56) [C8 (W (d_odr d))].

(* [comment removed for export] *)
Definition map_pre (m : word -> option byte) (B N ne : Z) (ks : list Z) (cur na fp : Z) : Prop :=
  rw_cells m (c_statics T + 56) [C8 (W (c_map T))]
  /\ rw_cells m (c_map T) [C8 (W B); C4 (W ne); C4 (W 0); C4 (W N)]
  /\ 8 <= N <= 2 ^ 20 /\ 0 <= ne /\ Z.of_nat (length ks) = N /\ Forall (fun key => 0 <= key < 2 ^ 64) ks
  /\ (forall b, 0 <= b < N -> ro_cells m (B + 32 * b) [C8 (W (nth (Z.to_nat b) ks 0))])
  /\ stk m B (B + 32 * N)
  /\ 0 < B /\ B + 32 * N <= 2 ^ 47 /\ (B + 32 * N <= l_ilo y \/ l_ihi y <= B) /\ B mod 8 = 0
  /\ (B + 32 * N <= shad y (l_ilo y) \/ shad y (l_ihi y) <= B)                  (* [comment removed for export] *)
  /\ (B + 32 * N <= cur \/ cur + 16 * na <= B)                                  (* [comment removed for export] *)
  /\ (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B).                               (* [comment removed for export] *)

Definition map_post (m' : word -> option byte) (B N : Z) (ks' : list Z) (ne' : Z) : Prop :=
  rw_cells m' (c_map T + 8) [C4 (W ne')]
  /\ (forall b, 0 <= b < N -> rw_cells m' (B + 32 * b) [C8 (W (nth (Z.to_nat b) ks' 0))]).

Definition walk_stmt : Prop :=
  forall (i n : Z) (ds : list desc) (N ne : Z) (ks ks' : list Z) (ne' : Z) (B cur lend size first fp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s2 s3 s6 s7 s10 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  let k := Z.of_nat (length ds) in
  let na := k + nind ds in
  let sp := fp - 0x10f0 in
  (* [comment removed for export] *)
  run y N ds ks ne = Some (ks', ne') ->
  1 <= k -> 0 <= i -> i + k < n -> c_tab T + 64 * n <= c_tabend T ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall j, 0 <= j < k -> desc_at m (c_tab T + 64 * (i + j)) (nth (Z.to_nat j) ds dflt)) ->
  List.NoDup (inds ds) ->
  (forall o, In o (inds ds) -> rw_cells m o [C1 (Z_to_bv 8 0)]) ->
  (* [comment removed for export] *)
  rw_cells m (c_inited T) [C1 (Z_to_bv 8 1)] ->
  ro_cells m (c_flags T + 24) [C4 (W 1)] -> ro_cells m (c_flags T + 85) [C1 (Z_to_bv 8 1)] -> ro_cells m (c_flags T + 100) [C4 (W 2)] ->
  ro_cells m (c_shcell T) [C8 (W (l_shb y))] ->
  ro_cells m (c_canpoison T) [C1 (Z_to_bv 8 1)] ->
  ro_cells m (c_msetcell T) [C8 (W (c_memset T))] ->
  ro_cells m (c_llaalign T) [C8 (W 8)] ->
  (* [comment removed for export] *)
  ro_cells m (fp - 0x10b0) [C8 (W n)] -> ro_cells m (fp - 0x10d0) [C8 (W (c_msetcell T))] ->
  stk m (fp - 0x10a8) (fp - 0x10a0) -> stk m (sp - 32) sp ->
  fp mod 16 = 0 -> l_ihi y <= sp - 32 -> shad y (l_ihi y) <= sp - 32 -> fp < 2 ^ 47 ->       (* [comment removed for export] *)
  (* [comment removed for export] *)
  stk m (shad y (l_ilo y)) (shad y (l_ihi y)) ->
  (* [comment removed for export] *)
  rw_cells m (c_lla T) [C8 (W lend); C8 (W cur)] -> 0 < cur -> cur + 16 * na <= lend -> lend < 2 ^ 47 ->
  stk m cur (cur + 16 * na) -> (cur + 16 * na <= l_ilo y \/ l_ihi y <= cur) ->
  (cur + 16 * na <= shad y (l_ilo y) \/ shad y (l_ihi y) <= cur) ->             (* [comment removed for export] *)
  (cur + 16 * na <= sp - 32 \/ fp <= cur) ->                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells m (c_statics T + 8) [C8 (W size); C8 (W first)] -> 1 <= size -> size + k < 2 ^ 63 ->
  (* [comment removed for export] *)
  (0 < nind ds -> map_pre m B N ne ks cur na fp) ->
  Mem.mem_inv segs m ->
  Exec.evt segs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s2' s6' s7' : word) (m' : word -> option byte),
      ms' = MState.MS (Frame.mkR ra' (W sp) gp tp t0' t1' t2' (W fp) (W (c_tab T)) a0' a1' a2' a3' a4' a5' a6' a7'
                         s2' s3 (W (c_shcell T)) (W 1) s6' s7' (W (c_flags T)) (W (c_statics T)) s10 (W (i + k)) t3' t4' t5' t6')
                      F (W (c_entry T)) fc None m' (seg_rom segs)
      /\ Frame.munch ([(fp - 0x10a8, fp - 0x10a0); (sp - 32, sp); (run_sh_lo y ds, run_sh_hi y ds);
                       (c_statics T + 8, c_statics T + 24); (c_lla T + 8, c_lla T + 16); (cur, cur + 16 * na)]
                      ++ ind_fp ds                                  (* [comment removed for export] *)
                      ++ (if 0 <? nind ds then [(c_map T + 8, c_map T + 12); (B, B + 32 * N)] else [])) m m'
      /\ Frame.wmono segs m m' /\ Mem.mem_inv segs m'
      /\ rw_cells m' (c_lla T + 8) [C8 (W (cur + 16 * na))]
      /\ rw_cells m' (c_statics T + 8) [C8 (W (size + k)); C8 (W (cur + 16 * na - 16))]
      /\ (0 < nind ds -> map_post m' B N ks' ne')
      (* [comment removed for export] *)
      /\ (forall x b, run_sh_lo y ds <= x < run_sh_hi y ds -> m (W x) = Some b -> m' (W x) = Some (Z_to_bv 8 (GSM.sh_upd y ds x (bv_unsigned b)))))
    (MState.MS (Frame.mkR ra (W sp) gp tp t0 t1 t2 (W fp) (W (c_tab T)) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (W (c_shcell T)) (W 1) s6 s7 (W (c_flags T)) (W (c_statics T)) s10 (W i) t3 t4 t5 t6)
               F (W (c_entry T)) fc None m (seg_rom segs)).

End Stmt.
End RGS.
