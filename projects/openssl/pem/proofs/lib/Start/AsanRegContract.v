(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec CatSim StoreOk AxSymExec3 AsanNodesLibSound.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module RGK.
Import RGM.

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).
#[local] Notation inr := LBNS.inr (only parsing).

Section Specs.
Variable SEGS : list Segment.
Variable T : ctab.
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).
#[local] Notation cell := (LBNS.cell SEGS) (only parsing).
#[local] Notation y := (c_lay T) (only parsing).

(* [comment removed for export] *)
Definition rw (M : word -> option byte) (a n : Z) : Prop := rd_ok M a n /\ wr_ok M a n.

Definition kdesc_at (M : word -> option byte) (g : Z) (d : desc) : Prop :=
  cell M g 8 (W (d_beg d)) /\ cell M (g + 8) 8 (W (d_size d)) /\ cell M (g + 16) 8 (W (d_swr d))
  /\ cell M (g + 40) 8 (W (d_dyn d)) /\ cell M (g + 56) 8 (W (d_odr d)).

Definition kmap_pre (M : word -> option byte) (B N ne : Z) (ks : list Z) (cur na fp : Z) : Prop :=
  cell M (c_statics T + 56) 8 (W (c_map T)) /\ wr_ok M (c_statics T + 56) 8
  /\ cell M (c_map T) 8 (W B) /\ cell M (c_map T + 8) 4 (W ne) /\ cell M (c_map T + 12) 4 (W 0) /\ cell M (c_map T + 16) 4 (W N)
  /\ wr_ok M (c_map T) 20
  /\ 8 <= N <= 2 ^ 20 /\ 0 <= ne /\ Z.of_nat (length ks) = N /\ Forall (fun key => 0 <= key < 2 ^ 64) ks
  /\ (forall b, 0 <= b < N -> cell M (B + 32 * b) 8 (W (nth (Z.to_nat b) ks 0)))
  /\ rw M B (32 * N)
  /\ 0 < B /\ B + 32 * N <= 2 ^ 47 /\ (B + 32 * N <= l_ilo y \/ l_ihi y <= B) /\ B mod 8 = 0
  /\ (B + 32 * N <= shad y (l_ilo y) \/ shad y (l_ihi y) <= B)
  /\ (B + 32 * N <= cur \/ cur + 16 * na <= B)
  /\ (B + 32 * N <= fp - 0x10f0 - 32 \/ fp <= B).

Definition kmap_post (M' : word -> option byte) (B N : Z) (ks' : list Z) (ne' : Z) : Prop :=
  cell M' (c_map T + 8) 4 (W ne') /\ (forall b, 0 <= b < N -> cell M' (B + 32 * b) 8 (W (nth (Z.to_nat b) ks' 0))).

(* [comment removed for export] *)
Definition rg_FP (fp cur na shlo shhi : Z) (os : list Z) (hasmap : bool) (B N : Z) (x : word) : Prop :=
  inr x (fp - 0x10a8) 8 \/ inr x (fp - 0x10f0 - 32) 32 \/ inr x shlo (shhi - shlo)
  \/ inr x (c_statics T + 8) 16 \/ inr x (c_lla T + 8) 8 \/ inr x cur (16 * na)
  \/ In (bv_unsigned x) os                                                    (* [comment removed for export] *)
  \/ (hasmap = true /\ (inr x (c_map T + 8) 4 \/ inr x B (32 * N))).

Definition regrun_contract : Prop :=
  forall regs M (i n : Z) (ds : list desc) (N ne : Z) (ks ks' : list Z) (ne' : Z) (B cur lend size first fp : Z),
    let k := Z.of_nat (length ds) in
    let na := k + nind ds in
    let sp := fp - 0x10f0 in
    getr regs 27%bv = W i -> getr regs 8%bv = W fp -> getr regs 2%bv = W sp -> getr regs 9%bv = W (c_tab T) -> getr regs 20%bv = W (c_shcell T) ->
    getr regs 21%bv = W 1 -> getr regs 24%bv = W (c_flags T) -> getr regs 25%bv = W (c_statics T) ->
    run y N ds ks ne = Some (ks', ne') ->
    1 <= k -> 0 <= i -> i + k < n -> c_tab T + 64 * n <= c_tabend T -> 0 <= c_tab T -> c_tab T + 64 * n < 2 ^ 40 ->
    (forall j, 0 <= j < k -> kdesc_at M (c_tab T + 64 * (i + j)) (nth (Z.to_nat j) ds (D 0 0 0 0 0))) ->
    List.NoDup (inds ds) -> (forall o, In o (inds ds) -> cell M o 1 (W 0)) -> wr_ok M (l_odr_lo y) (l_odr_hi y - l_odr_lo y) ->
    (* [comment removed for export] *)
    cell M (c_inited T) 1 (W 1) -> wr_ok M (c_inited T) 1 ->
    cell M (c_flags T + 24) 4 (W 1) -> cell M (c_flags T + 85) 1 (W 1) -> cell M (c_flags T + 100) 4 (W 2) ->
    cell M (c_shcell T) 8 (W (l_shb y)) -> cell M (c_canpoison T) 1 (W 1) -> cell M (c_msetcell T) 8 (W (c_memset T)) -> cell M (c_llaalign T) 8 (W 8) ->
    (* [comment removed for export] *)
    cell M (fp - 0x10b0) 8 (W n) -> cell M (fp - 0x10d0) 8 (W (c_msetcell T)) ->
    rw M (fp - 0x10a8) 8 -> rw M (sp - 32) 32 ->
    fp mod 16 = 0 -> l_ihi y <= sp - 32 -> shad y (l_ihi y) <= sp - 32 -> fp < 2 ^ 47 ->
    (* [comment removed for export] *)
    rw M (shad y (l_ilo y)) (shad y (l_ihi y) - shad y (l_ilo y)) ->
    (* [comment removed for export] *)
    cell M (c_lla T) 8 (W lend) -> cell M (c_lla T + 8) 8 (W cur) -> wr_ok M (c_lla T) 16 ->
    0 < cur -> cur + 16 * na <= lend -> lend < 2 ^ 47 -> rw M cur (16 * na) ->
    (cur + 16 * na <= l_ilo y \/ l_ihi y <= cur) -> (cur + 16 * na <= shad y (l_ilo y) \/ shad y (l_ihi y) <= cur) ->
    (cur + 16 * na <= sp - 32 \/ fp <= cur) ->
    (* [comment removed for export] *)
    cell M (c_statics T + 8) 8 (W size) -> cell M (c_statics T + 16) 8 (W first) -> wr_ok M (c_statics T + 8) 16 -> 1 <= size -> size + k < 2 ^ 63 ->
    (* [comment removed for export] *)
    (0 < nind ds -> kmap_pre M B N ne ks cur na fp) ->
    (* [comment removed for export] *)
    (forall s, In s SEGS -> seg_writable s = false -> forall z, Z.of_N (seg_base s) <= z < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> M (W z) = None) ->
    exists regs' M',
      msteps SEGS (mkst regs (W (c_entry T)) M (seg_rom SEGS)) (mkst regs' (W (c_entry T)) M' (seg_rom SEGS))
      /\ (forall r : bv 5, ~ In (ridx r) rg_fresh -> ridx r <> 27%nat -> getr regs' r = getr regs r)
      /\ getr regs' 27%bv = W (i + k)
      /\ cell M' (c_lla T + 8) 8 (W (cur + 16 * na))
      /\ cell M' (c_statics T + 8) 8 (W (size + k)) /\ cell M' (c_statics T + 16) 8 (W (cur + 16 * na - 16))
      /\ (0 < nind ds -> kmap_post M' B N ks' ne')
      /\ (forall x, ~ rg_FP fp cur na (run_sh_lo y ds) (run_sh_hi y ds) (inds ds) (0 <? nind ds) B N x -> M' x = M x)
      /\ mem_grows M M'
      (* [comment removed for export] *)
      /\ (forall x b, run_sh_lo y ds <= x < run_sh_hi y ds -> 0 <= x < 2 ^ 47 -> M (W x) = Some b -> M' (W x) = Some (Z_to_bv 8 (GSM.sh_upd y ds x (bv_unsigned b)))).

End Specs.
End RGK.
