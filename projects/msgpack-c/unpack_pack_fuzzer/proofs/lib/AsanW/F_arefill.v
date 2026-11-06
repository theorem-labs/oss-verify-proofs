(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aensure F_apopulate.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_agetfrom.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_arefill.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition refill_entry := 0x41b70.
End CANSEC1.
Notation REFILL_STACK := 672 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma v_divuw_lit : forall x y, 0 <= x < 2^31 -> 0 < y < 2^31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small x) by lia. f_equal.
  assert (B : 0 <= x / y <= x) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

Definition arec_hdr (L : alayout) (m : amem) (j cnt mc cs : Z) : Prop :=
  rw_cells asegs m (acache_addr L j) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

End CANSEC2.
Ltac zfact := first [ split; zfact | vm_compute; first [reflexivity | discriminate | intros ?; discriminate] ].
Section CANSEC3. Context {rc : runConstT} {ov : annOV}.
Lemma mc_le4 : forall i, 1 <= i <= 4 -> max_cached i = 16 /\ 8 <= 1024 / (32 * i).
Proof.
  intros i Hi. assert (E : i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_mid : forall i, 5 <= i <= 16 -> max_cached i = 2 * (1024 / (32 * i)) /\ 1 <= 1024 / (32 * i) < 8.
Proof.
  intros i Hi. assert (E : i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_big : forall i, 17 <= i <= 30 -> max_cached i = 2 /\ 768 <= size_of_class i <= 65536 /\ 1024 / size_of_class i <= 1.
Proof.
  intros i Hi. assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_31 : max_cached 31 = 16. Proof. vm_compute. reflexivity. Qed.

Lemma size_formula2 : forall i, 17 <= i <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) = Z_to_bv 64 (size_of_class i).
Proof.
  intros i Hi.
  assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

Fixpoint ic_W (L : alayout) (i : Z) (d : nat) : list (Z * Z) :=
  match d with O => [] | Datatypes.S d' => (acache_addr L i + 4, acache_addr L i + 16) :: ic_W L (i + 1) d' end.

Lemma munch_cons_trans : forall p W m m1 m', munch [p] m m1 -> munch W m1 m' -> munch (p :: W) m m'.
Proof.
  intros [lo hi] W m m1 m' A B. eapply munch_trans; [eapply munch_weaken; [| exact A] | eapply munch_weaken; [| exact B]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; tauto.
Qed.

Lemma ic_W_disjoint_below : forall L i d A n, A + n <= acache_addr L i + 4 -> disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH. unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_gen : forall L i d A n, (A + n <= acache_addr L i + 4 \/ al_t L + 2768 <= A) -> i + Z.of_nat d <= 32 -> 1 <= i ->
  disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H Hd Hi; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_chunks : forall L i d c, disjoint_from (ic_W L i d) (acache_addr L c + 16) 64.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i c; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr; lia|]. apply IH.
Qed.

End CANSEC3.
Ltac icdj tac := cbn [disjoint_from cells_size csize Nat.add length]; split; [tac | first [apply ic_W_disjoint_chunks | apply ic_W_disjoint_gen; [tac | clear; cbn; lia | clear; lia]]].

Section CANSEC4. Context {rc : runConstT} {ov : annOV}.
Lemma ic_W_outside : forall L i d x, (x < acache_addr L i + 4 \/ al_t L + 2768 <= x) -> i + Z.of_nat d <= 32 -> 1 <= i -> outside (ic_W L i d) x.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i x Hx Hd Hi; cbn [ic_W outside]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma initcache_loop_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  iclr (al_t L) 4096 ->
  evtF asegs RNG (fun ms' => exists a1' a3' a5' t3' t4' t5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 a1' a2 a3' a4 a5' (Z_to_bv 64 15) (Z_to_bv 64 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x41c68) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41c14) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT TIC; [lia|]. band_lin.
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t5x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
               (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t5x t6)
          F (Z_to_bv 64 0x41bf0) fc None mm (seg_rom asegs)))
  end.
  { intros q t5x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.
    setreg 29 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 13 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1 TIC; lia. }
      cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).
  {
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.
    step. step. step.
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 29 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).
  step.
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).
  -
    step.
    setreg 29 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  -
    do 7 zstep.
    setreg 28 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.
    setreg 29 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

Lemma max_cached_range : forall c, 1 <= c <= 31 -> 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
  intros c Hc. unfold max_cached.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.

Definition KKref {R} (k : astate -> bool -> AM R) (c n : Z) (st2 : astate) : AM R :=
  k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true.

Definition refill_tail_ret (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = put_cls c (get_cls st2 c) st1)
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ (exists bfl : byte, rw_cells asegs m' (RI + 68) [C1 bfl] /\ (c = K_BATCH_CLASS -> bfl = Z_to_bv 8 0))
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma refill_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41b90) fc None m (seg_rom asegs)).
Proof.
  intros until fr0. cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  set (n := max_cached c / 2) in *.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  zstep.
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.
  step.
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  destruct GR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR & JR & GC2 & ST2E
                  & MU2 & WM2 & MI2 & ST2 & MTX2 & REG2 & EXH2 & STN2 & STATS2 & LSJ2 & STM2 & CH2 & AZU2 & AZF2 & MC2).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 269232)) with (Z_to_bv 64 269232 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exists (Z_to_bv 8 0); split; [exact EXH2| reflexivity]|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].
Qed.

Definition refill_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono asegs m m1
  /\ refill_tail_ret L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Lemma init_cache_cinit : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma init_cache_cls : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma init_cache_space : forall st, a_space_beg (init_cache st) = a_space_beg st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma refill_tailK : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->

  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x41b90) fc None m1 (seg_rom asegs)).
Proof.
  intros until fr0. cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  assert (WOK1 : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).

  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.
  eapply (refill_tail_spec RNG k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  destruct TR as (_ & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & MUB & _ & _ & NC0 & _ & _ & NEWB & NEWM & _ & NLE & _ & _ & _ & _ & MUT & WMT & _).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  destruct B1 as (B1 & B2 & B3 & B4).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.

Lemma refill_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->

  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA RECS CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  rewrite cache_refill_tree_gfa. cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).

  pose proof (@refill_tailK RNG R k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.
  step. step. step.
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  -
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  -
    rewrite sx32_lit by (clear; lia).
    step. if_lit.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).
    step.
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End CANSEC4.
End F_arefill.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKitR.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amaybe.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acdrain.
Module F_acdealloc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom. Import F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition cdealloc_entry : Z := 0x3f3dc.
End CANSEC1.
Notation CDEALLOC_STACK := 688 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma initcache_loop2_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a1 a2 a3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv asegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  evtF asegs RNG (fun ms' => exists a4' a5' a6' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 a4' a5' a6' (Z_to_bv 64 15)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4' t5' t6') F (Z_to_bv 64 0x3f560) fc None m' (seg_rom asegs)
      /\ munch (ic_W L i d) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6)
        F (Z_to_bv 64 0x3f50c) fc None m (seg_rom asegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT; [lia|]. band_lin.
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.

  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t6x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells asegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv asegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono asegs m mm ->
    evtF asegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t6x)
          F (Z_to_bv 64 0x3f4e8) fc None mm (seg_rom asegs)))
  end.
  { intros q t6x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.
    setreg 30 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.
    zstep.
    setreg 14 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1; lia. }
      cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells asegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).
  {
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.
    step. step. step.
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 30 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).
  step.
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).
  -
    step.
    setreg 30 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  -
    do 7 zstep.
    setreg 29 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.
    setreg 30 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

Definition cdmain_post (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sta' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
              (al_t L + 2784, al_t L + 2792)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 (k0 + 1)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr asegs m' (acache_addr L c + 16) (upd chunks (Z.to_nat k0) (Z_to_bv 64 ((P - aregion L c) / 16)))
    /\ rw_cells asegs m' (al_t L + 2784) [C8 sta'].

Lemma cd_main_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (sta : word),
  stk asegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 (al_space_beg L))] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 k0); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr asegs m (acache_addr L c + 16) chunks -> length chunks = 16%nat ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  1 <= c < K_NUM_CLASSES -> 0 <= k0 < 16 -> 0 <= mc < 2^31 -> 0 <= csz < 2^63 ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  iclr (al_t L) 4096 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_t L) 4096 ->
  evtF asegs RNG (cdmain_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc L c k0 mc csz P lo chunks m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1x
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 k0) a5 a6 a7
             s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3f420) fc None m (seg_rom asegs)).
Proof.
  intros until sta. intros ST CEIL LO MI FR ISB CR CH LCH STA HC K0 MC CSZ P0 P1 SP1 SP2 T0 T1 TAL TI RIMG RSTK RT. band_lin.
  unfold AINSTANCE, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
                          (al_t L + 2784, al_t L + 2792)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  step.
  zstep. zstep. zstep. zstep. zstep.
  step.
  zstep. zstep. zstep. zstep. zstep.
  setreg 12 (Z_to_bv 64 (acache_addr L c + 4 * k0)) ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear -K0; lia); f_equal;
      change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
  setreg 13 (Z_to_bv 64 ((P - aregion L c) / 16))
    ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; change (2^32) with 4294967296; f_equal; f_equal;
          rewrite RBE; rewrite (Z.mod_small (c * 4294967296)) by (clear -HC; lia);
          rewrite (Z.mod_small (P - c * 4294967296)) by (clear -HC P0 P1 SP1 SP2 RBE; lia);
          rewrite Z.mod_small by (clear -HC P0 P1 SP1 SP2 RBE; lia); clear; lia).
  box CH. box STA. box ISB.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  step.
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STA MUc WMc ltac:(rewrite CAE; clear -HC; lia).
  carry ISB MUc WMc ltac:(rewrite CAE; clear -HC TI; lia).
  clear MUc WMc.
  pose proof (u32arr_store_ok asegs _ (acache_addr L c + 16) _ k0 (wa (acache_addr L c + 16 + 4 * k0)) CH ltac:(rewrite LCH; clear -K0; lia) eq_refl) as SOK.
  box CR. box STA. box ISB. box FR.
  snapshot [(acache_addr L c + 16, acache_addr L c + 80)]%Z MUa WMa.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    pose proof (u32arr_write asegs mm (acache_addr L c + 16) _ k0 v CH ltac:(rewrite LCH; clear -K0; lia)) as CH2
  end.
  clear CH. store_done. try clear SOK.
  carry CR MUa WMa ltac:(clear; lia). carry STA MUa WMa ltac:(rewrite CAE; clear -HC; lia). carry ISB MUa WMa ltac:(rewrite CAE; clear -HC TI; lia).
  carry FR MUa WMa ltac:(rewrite CAE; clear -HC T1 SPR CEIL LO; lia). clear MUa WMa.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2784)) = true) by (pose proof atop_range as AR; apply amo_alignedD_intro; [clear -TI T1 AR; lia| clear -TAL; Z.div_mod_to_equations; lia]).
  box CH2. box CR. box ISB.
  snapshot [(al_t L + 2784, al_t L + 2792)]%Z MUb WMb.
  amo_stepA AMO.
  carry CH2 MUb WMb ltac:(rewrite ?upd_length, LCH, CAE; clear -HC; lia). carry CR MUb WMb ltac:(rewrite CAE; clear -HC; lia). carry ISB MUb WMb ltac:(clear -TI; lia).
  clear MUb WMb.
  do 8 step.
  release_frame FR ST (bv_unsigned sp).
  unfold cdmain_post. finish.
  all: try eassumption.
Qed.

Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma a_cinit_init_cache : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite a_cinit_init_cache. reflexivity. Qed.
Lemma put_cls_put_cls : forall c x y st, put_cls c x (put_cls c y st) = put_cls c x st.
Proof. intros c x y st. unfold put_cls, set_cls. cbn. f_equal. rewrite insert_insert. destruct (decide (c = c)) as [|NE]; [reflexivity| exfalso; apply NE; reflexivity]. Qed.
Lemma get_cls_put_cls_same : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. apply get_cls_put_cls_eq. Qed.

Definition cd_W (L : alayout) (sp : Z) (c nf mfa mfa' : Z) : list (Z * Z) :=
  let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  ([(sp - 688, sp)] ++ ic_W L 1 31 ++
   [(CA, CA + 4); (CA + 16, CA + 80); (al_t L + 2784, al_t L + 2792); (al_t L + 2800, al_t L + 3168);
    (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
    (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)])%Z.

Definition cdealloc_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c P lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let mc := max_cached c in let half := mc / 2 in let cnt := c_count r in
  fp_le RNG RNG' /\
  exists (drained : bool) mfa' sj' (sta' : word),
  let nf' := if drained then nf + half else nf in
  let cnt' := if drained then cnt - half + 1 else cnt + 1 in

     drained = (a_cinit st && (cnt =? mc))%bool
  /\ get_cls stX c = mkAClass (c_mapped_user r) (c_allocated_user r) nf' mfa' cnt'
  /\ stX = put_cls c (get_cls stX c) (init_cache st)
  /\ (   mfa' = mfa
      \/ (drained = true /\ mfa < 4 * (nf + half) /\ mfa' = rup (4 * (nf + half)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf' <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0

  /\ munch (cd_W L (bv_unsigned sp) c nf mfa mfa') m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)

  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (c_count (get_cls st j)) (max_cached j) (size_of_class j))
  /\ arec_hdr L m' c cnt' (max_cached c) (size_of_class c)
  /\ u32arr asegs m' (CA + 16) (upd chunks (Z.to_nat (cnt' - 1)) (Z_to_bv 64 ((P - aregion L c) / 16)))
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf'); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2784) [C8 sta']
  /\ (drained = true -> u32arr asegs m' (FA + 4 * nf) (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)))
  /\ junk_at m' (FA + 4 * nf') (mfa' - 4 * nf')
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma cdealloc_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr asegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells asegs m (al_t L + 2784) [C8 sta] ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS asegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros until sta. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF SBE HC CNTS NF MFA MFAM NFN P0 P1
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).
  pose proof atop_range as AR.
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdealloc_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCEV].
  pose proof (CNTS c ltac:(clear -HC; lia)) as CNTc. fold nf in CNTc.
  pose proof (RECS c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  box TCX. box SCX. box TSP.
  pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. clear CR.
  do 7 step.
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RECS0 : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
    [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MUN | exact WM |];
      cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -Hj SPR CEIL LO T0 T1; lia |]
  end.
  clear RECS.
  eapply junk_frame in J72; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia].
  eapply junk_frame in FJ; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite FAE; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF0 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC SPR CEIL LO MFA NF; Z.div_mod_to_equations; lia |];
    assert (MC0 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO; lia |]; apply Forall_nil |]
  end.
  clear AZF MC.
  pose proof (RECS0 c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear -HC; lia); clear -KZ HC; lia|].
  step. step. if_cases K32; zify_cond K32; [exfalso; rewrite ?unsigned_lit in K32 by (clear -HC; lia); clear -K32 HC; lia|].
  step. zstep. zstep.
  setreg 8 (Z_to_bv 64 (acache_addr L c)) ltac:(rewrite CAE; f_equal; clear; lia).
  step.
  unfold max_count in *.
  destruct (a_cinit st) eqn:CI.
  -
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step. if_cases KM; zify_cond KM; [exfalso; rewrite ?unsigned_lit in KM by (clear -MCR; lia); clear -KM MCR; lia|].
    step.
    rewrite (sx32_lit (c_count (get_cls st c))) by (clear -CNTc MCR; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -CNTc MCR; lia).
    +
      do 7 step.
      step.
      apply evtF_done.
      unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with true by (symmetry; apply Z.eqb_eq; exact KD).
      name_sp sp (-48).
      eapply cdrain_spec with (lo := lo) (L := L) (sj := sj) (chunks := chunks) (cnt := c_count (get_cls st c)) (mc := max_cached c) (csz := size_of_class c);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- m3_cells _ _ => exact MC0
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZF0
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              clear KONT; fold nf mfa; first [assumption | clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNTc KD MCR; lia]).

      intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DR.
      unfold cdrain_ret in DR. cbv zeta in DR. destruct DR as (md & MU01 & WM01 & RR & CR2 & CH2 & ST2).
      pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
      destruct RR0 as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & GC2 & ST2E & MU2 & WM2 & MI2 & _ & MTX2 & REG2 & J722 & STATS2 & LSJ2 & SRC2 & JR2 & AZF2 & MC2).
      rewrite Hsp in *. unname_sp.
      rewrite ?unsigned_lit in MU2 by (clear -SPR CEIL LO; lia).
      rewrite ?unsigned_lit in ST2 by (clear -SPR CEIL LO; lia).
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
      assert (SHF : shad (afreearr L c + mfa) + shlen (new - mfa) <= 0x10007fff8000).
      { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE MCR. Z.div_mod_to_equations. lia. }
      assert (SHB2 : 2148261376 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).
      xport FR MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T1 HC; lia).
      xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      xport STA MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      xport STA MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
      replace (ret_pc (Z_to_bv 64 259468)) with (Z_to_bv 64 259468 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      iprefix.
      step. step. step. step.
      step.
      rewrite (sx32_lit (c_count (get_cls st c) - max_cached c / 2)) by (clear -CNTc MCR KD; lia).
      step.
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 877688 _ => exact ISB2
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH2
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. cbv beta. eapply KONT.

      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa.
      split; [exact FPLE|].
      exists true, new, sj', sta'. cbn [andb].
      rewrite CI. cbn [andb].
      split; [symmetry; apply Z.eqb_eq; exact KD|].
      assert (GCX : get_cls (put_cls c (cls_set_count (c_count (get_cls st2 c) - max_cached c / 2 + 1)
                        (cls_set_num_freed (c_num_freed (get_cls st2 c) + max_cached c / 2) (get_cls st2 c))) st2) c
                    = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) (nf + max_cached c / 2) new (c_count (get_cls st c) - max_cached c / 2 + 1)).
      { rewrite get_cls_put_cls_eq, GC2. reflexivity. }
      split; [exact GCX|].
      split. { rewrite GCX. unfold init_cache. rewrite CI. rewrite GC2. cbn [cls_set_count cls_set_num_freed c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count].
               destruct ST2E as [E|E]; rewrite E; [reflexivity|]. rewrite GC2, put_cls_put_cls. reflexivity. }
      split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
               split; [reflexivity|]. split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
               eapply fill_frame; [exact FILL | exact MU3 | exact WM3 |]. intros _. cbn [disjoint_from].
               clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF CAE. lia. }
      split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU01]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU2]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia). }
      split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2| exact WM3]]]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr.
               eapply cells_frame; [| exact MU3 | exact WM3 |].
               { eapply cells_frame; [| exact MU2 | exact WM2 |].
                 { eapply cells_frame; [exact (RECS0 j Hj) | exact MU01 | exact WM01 |].
                   cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
                 cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. ub TSP; clear -Hj NE SPR CEIL LO T0 T0k SHB2 T1 HC SP1 SP2 RIE FAE NF MFA NEWB SHF Y; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) - max_cached c / 2 + 1 - 1) with (c_count (get_cls st c) - max_cached c / 2) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J722 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS2 | exact MU3 | exact WM3 | rewrite LSJ2; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ2|]. split; [exact STA3|].
      split. { intros _. eapply u32arr_frame; [exact SRC2 | exact MU3 | exact WM3 |]. rewrite length_firstn, length_skipn, LCH. cbn [disjoint_from]. rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR CNTc NFN; lia. }
      split; [eapply junk_frame; [exact JR2 | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR NEWB; lia]|].
      assert (SHF3 : 2148261376 <= shad (afreearr L c + new) /\ shad (afreearr L c + new) + shlen (536870912 - new) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF NEWB MCR AR; Z.div_mod_to_equations; lia).
      split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
    +
      pose proof MC0 as MC0'. destruct MC0' as (_ & _ & _ & _ & _ & _ & _ & ISB0 & _).
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 877688 _ => exact ISB0
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with false by (symmetry; apply Z.eqb_neq; exact KD).
      eapply KONT.

      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI. cbn [andb].
      split; [apply fp_le_refl|].
      exists false, mfa, sj, sta'.
      split; [symmetry; apply Z.eqb_neq; exact KD|].
      split; [rewrite get_cls_put_cls_eq; reflexivity|].
      split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
      split; [left; reflexivity|].
      split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
      split; [eapply wmono_trans; [exact WM| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS0 j Hj) | exact MU3 | exact WM3 |].
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) + 1 - 1) with (c_count (get_cls st c)) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ|]. split; [exact STA3|].
      split; [intros; discriminate|].
      split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
      assert (SHF3 : 2148261376 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
      split; [eapply azero_frame; [exact AZF0 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC0 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
  -
    replace (if false then max_cached c else 0) with 0 by reflexivity. rewrite (sx32_lit 0) by (clear; lia).
    assert (CNT0 : c_count (get_cls st c) = 0) by (clear -CNTc; lia).
    step. if_cases KM; zify_cond KM; [| exfalso; rewrite ?unsigned_lit in KM by (clear; lia); clear -KM; lia].
    do 9 step.
    setreg 14 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * 1)) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(f_equal; clear; lia).
    box FR. box STA. box CH. box MTX. box REG.
    eapply evtF_cut.
    { eapply (initcache_loop2_spec RNG 31 1 L (fun j => c_count (get_cls st j))); try reflexivity.
      - clear; lia.
      - intros j Hj. pose proof (RECS0 j Hj) as Rj. cbn in Rj. exact Rj.
      - assumption.
      - exact T0.
      - atop_facts; exact T1.
      - exact RT. }
    cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & RECS3).
    carry FR MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia]).
    carry STA MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    carry CH MU2 WM2 ltac:(rewrite LCH; apply ic_W_disjoint_chunks).
    carry MTX MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    carry REG MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    pose proof (stk_transport_disjoint asegs _ _ m2 _ _ ST MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia])) as ST2.
    eapply junk_frame in J72; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]].
    eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite FAE; unfold acache_addr; clear -SP1 SP2 HC Y NF MFA; lia| clear; cbn; lia| clear; lia]].
    xport STATS MU2 WM2 ltac:(rewrite LSJ; apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    assert (AZF2 : azero m2 (shad (afreearr L c + mfa)) (shlen (536870912 - mfa))).
    { eapply azero_frame; [exact AZF0 | exact MU2 | exact WM2 |]. intros _. assert (SHF3 : 2148261376 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
      apply ic_W_disjoint_gen; [unfold acache_addr; clear -SHF3 T0k; lia| clear; cbn; lia| clear; lia]. }
    assert (MC2 : m3_cells L m2).
    { eapply m3_cells_frame; [exact MC0 | exact MU2 | exact WM2 |]. unfold AIMG_HI, AIMG_LO. ub TCX. cbn [ic_W]. unfold acache_addr.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC T0 T1 Y; lia |]). apply Forall_nil. }
    clear ST MI AZF0 MC0.
    pose proof (RECS3 c ltac:(clear -HC; lia)) as CR2. unfold arec_hdr in CR2. rewrite CNT0 in CR2.
    step.
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step.
    rewrite (sx32_lit 0) by (clear; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -MCR; lia); [| exfalso; clear -KD MCR; lia].
    pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
    pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
    eapply evtF_cut.
    { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks) (k0 := 0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ 877688 _ => exact ISB2
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => exact LCH
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (al_t _) _ => exact RT
       | |- iclr _ _ => exact TIC
       end;
      unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
      first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
    cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
    apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. cbn [a_cinit set_cinit].
    change (get_cls (set_cinit true st) c) with (get_cls st c). fold nf. rewrite CNT0.
    replace (0 =? max_cached c) with false by (symmetry; apply Z.eqb_neq; clear -MCR; lia).
    eapply KONT.

    unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI, CNT0. cbn [andb].
    split; [apply fp_le_refl|].
    exists false, mfa, sj, sta'.
    split; [reflexivity|].
    split; [rewrite get_cls_put_cls_eq; reflexivity|].
    split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
    split; [left; reflexivity|].
    split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    split. { unfold cd_W. cbv zeta. cbn [ic_W app].
             eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]; cbn [ic_W]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS3 j Hj) | exact MU3 | exact WM3 |].
             cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
    split; [exact CR3|].
    split; [eapply u32arr_addr_eq; [exact CH3| reflexivity]|].
    split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
    split; [exact LSJ|]. split; [exact STA3|].
    split; [intros; discriminate|].
    split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
    assert (SHF3 : 2148261376 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
    split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
    eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
Qed.
End CANSEC2.
End F_acdealloc.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMalloc_iface AEmbRep AFrameD AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apopulate_x.
Module F_arefill_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom_x. Import F_arefill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

Notation REFILL_STACK_X := 1504 (only parsing).

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition refill_tail_ret_x (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells asegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr asegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = exh_clear c (put_cls c (get_cls st2 c) st1))
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st2 then 1 else 0))]
  /\ rw_cells asegs m' (RI + 72) [C8 stn']
  /\ u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells asegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr asegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma refill_tail_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st1 then 1 else 0))] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells asegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st1 m -> (let '(_, cap0, _) := a_emb st1 in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st1 in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st1 RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      xfalse_ret L RESV RNG sp REFILL_STACK_X st1 c lo m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret_x L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree_x RESV st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41b90) fc None m (seg_rom asegs)).
Proof.
  intros until fr0. cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  set (n := max_cached c / 2) in *.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  zstep.
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.
  step.
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec_x with (lo := lo) (L := L) (RESV := RESV);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELRO
       | |- exh_cells _ => exact XC | |- emb_cells _ _ => exact EC | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG
       | |- bv_unsigned _ < 2 ^ 63 => rewrite Hsp; pose proof atop_range; clear -SP63 SPR CEIL LO; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  1: {
    intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' XF.
    unfold xfalse_ret in XF. cbv zeta in XF.
    destruct (a_emb st1) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct XF as (FPLE & STREL & EC2 & ERNG2 & XC2 & MTX2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    unname_sp. pose proof atop_range as ATR.
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
    assert (RIHI : aregion_info L c + 128 <= ATOP).
    { unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. clear -SP2 HC. lia. }
    assert (B0 : cap0 = 0 \/ (0 < cap0 /\ d0 + cap0 <= ATOP)) by (destruct (emb_cells_top st1 m d0 cap0 sz0 EC EE) as [Z0|(CP0 & _ & TB0)]; [left| right; split]; assumption).
    assert (B2 : cap2 = 0 \/ (0 < cap2 /\ d2 + cap2 <= ATOP)) by (destruct (emb_cells_top st2 m2 d2 cap2 sz2 EC2 EE2) as [Z2|(CP2 & _ & TB2)]; [left| right; split]; assumption).
    eapply (cells_frameO _ _ m2) in FR; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RIHI ATR B0 B2 TP1; lia].
    replace (ret_pc (Z_to_bv 64 269232)) with (Z_to_bv 64 269232 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    iprefix.
    step. if_lit.
    lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
    refresh RSTK. do 5 step.
    lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    subst PP. apply evtF_done. eapply KF.
    unfold xfalse_ret. cbv zeta. rewrite EE, EE2.
    split; [exact FPLE|]. split; [exact STREL|]. split; [exact EC2|]. split; [exact ERNG2|]. split; [exact XC2|]. split; [exact MTX2|]. split; [exact FLG2|].
    split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TP1]]].
             eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    split; [exact MI2| assumption]. }

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  destruct GR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR & JR & GC2 & ST2E
                  & MU2 & WM2 & MI2 & ST2 & MTX2 & REG2 & EXH2 & STN2 & STATS2 & LSJ2 & STM2 & CH2 & AZU2 & AZF2 & MC2).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 269232)) with (Z_to_bv 64 269232 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -32) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].
Qed.

Definition refill_ret_x (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono asegs m m1
  /\ refill_tail_ret_x L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Definition refill_ret_false (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo cntc : Z) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK_X, bv_unsigned sp) :: ic_W L 1 31)%Z m m1
  /\ xfalse_ret L RESV RNG sp REFILL_STACK_X (init_cache st) c lo m1 st2 RNG' m'
  /\ rw_cells asegs m' (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 (size_of_class c))]
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Definition cache_refill_tree_x {R} (RESV : list (Z * Z)) (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array_x ATOP RESV st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).
Lemma cache_alloc_x_unfold : forall {R} RESV st c (k : astate -> bool -> AM R),
  cache_alloc_x ATOP RESV st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree_x RESV st c k).
Proof. intros. reflexivity. Qed.
Lemma cache_refill_tree_x_gfa : forall {R} RESV st c (k : astate -> bool -> AM R), c <> K_BATCH_CLASS ->
  cache_refill_tree_x RESV st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree_x RESV st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof.
  intros R RESV st c k NC. unfold cache_refill_tree_x, gfa_tree_x, gfa_take, populate_free_array_x. cbv zeta.
  replace (c =? K_BATCH_CLASS) with false by (symmetry; apply Z.eqb_neq; exact NC). reflexivity.
Qed.

Lemma refill_tailK_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->
  pcov RESV (al_t L) (al_t L + 4096) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_false L RESV RNG sp st c lo cntc cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->

  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (gfa_tree_x RESV st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x41b90) fc None m1 (seg_rom asegs)).
Proof.
  intros until fr0. cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG TRES TOLD KF KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  assert (WOK1 : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).

  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.

  pose proof atop_range as ATR.
  assert (IC1 : img_clear ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { apply img_clear_band. eapply Forall_impl; [| exact WOK1]. cbv beta. intros iv [X _]. exact X. }
  assert (EE1 : a_emb st1 = a_emb st) by (rewrite E1; apply init_cache_emb).
  assert (XM1 : exh_mem c st1 = exh_mem c st) by (rewrite E1; apply init_cache_exh).
  assert (RELRO1 : arelro m1) by (exact (arelro_frameO m m1 _ RELRO MU1 IC1)).
  assert (XC1 : exh_cells m1) by (exact (exh_cells_frameO m m1 _ XC MU1 IC1)).
  assert (EC1 : emb_cells st1 m1).
  { assert (X : emb_cells st m1).
    { apply (emb_cells_frameO st m m1 _ EC MU1 IC1). destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE0.
      destruct (emb_cells_top st m d0 cap0 sz0 EC EE0) as [Z0|(CP0 & _ & TB0)]; [intros x Hx; exfalso; clear -Z0 Hx; lia|].
      intros x Hx. cbn [outside]. split; [clear -Hx TB0 LO CEIL; lia|].
      apply ic_W_outside; [unfold acache_addr; clear -Hx TOLD CP0; lia| clear; cbn; lia| clear; lia]. }
    unfold emb_cells in *. rewrite EE1. exact X. }
  rewrite <- EE1 in CAPB, RIOLD. rewrite <- XM1 in EXH.
  assert (ERNG1 : emb_rng st1 RNG) by (unfold emb_rng in *; rewrite EE1; exact ERNG).
  eapply (refill_tail_spec_x RNG RESV k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELRO1
       | |- exh_cells _ => exact XC1 | |- emb_cells _ _ => exact EC1 | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG1
       | |- bv_unsigned _ < 2 ^ 63 => exact SP63
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  1: {
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' XF. eapply KF. exists m1.
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x [OA OB]; split; [clear -OA; lia| exact OB]|]. split; [rewrite <- E1; exact XF|].
    unfold xfalse_ret in XF. cbv zeta in XF. destruct (a_emb st1) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct XF as (FPLE & STREL & EC2 & ERNG2 & XC2 & MTX2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    rewrite <- EE1 in TOLD. cbv beta iota in TOLD.
    assert (CLT : forall d cap, emb_prov RESV st1 d0 cap0 d cap -> cap <= 0 \/ al_t L + 4096 <= d \/ d + cap <= al_t L).
    { intros d cap [(-> & ->)|AV]; [clear -TOLD; lia|].
      destruct (Z_le_gt_dec cap 0) as [LE0|GT0]; [left; exact LE0| right].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      pose proof (pcov_clear _ _ _ _ _ TRES AV ltac:(clear; lia) ltac:(clear -GT0; lia)) as C. clear -C. lia. }
    pose proof (CLT d1 cap1 PV1) as CL1. pose proof (CLT d2 cap2 PV2) as CL2.
    assert (REC_T : forall j cs, 1 <= j <= 31 -> rw_cells asegs m1 (acache_addr L j) cs -> Z.of_nat (cells_size cs) = 16 -> rw_cells asegs m' (acache_addr L j) cs).
    { intros j cs Hj RC SZ. eapply cells_frameO; [exact RC| exact MU2|]. rewrite SZ. intros x Hx. cbn [outside]. unfold AEMB, acache_addr in *.
      ub TSP. rewrite RIE. repeat split; try exact I; clear -Hx Hj SPR CEIL LO SP1 SP2 HC T0 T1 TIC TB Y TOLD CL1 CL2 ATR; lia. }
    split; [apply (REC_T c _ ltac:(clear -HC; lia) REC1 eq_refl)|].
    intros j Hj Hjc. unfold arec_hdr. apply (REC_T j _ Hj (RECS1 j Hj Hjc) eq_refl). }

  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  destruct TR as (_ & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & MUB & _ & _ & NC0 & _ & _ & NEWB & NEWM & _ & NLE & _ & _ & _ & _ & MUT & WMT & _).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  destruct B1 as (B1 & B2 & B3 & B4).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.

Lemma refill_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  c <> K_BATCH_CLASS ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells asegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells asegs m (RI + 72) [C8 stn] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  u32arr asegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr asegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->

  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->
  pcov RESV (al_t L) (al_t L + 4096) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_false L RESV RNG sp st c lo (cnt c) cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (cache_refill_tree_x RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros NC24 ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA RECS CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG TRES TOLD KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  rewrite (cache_refill_tree_x_gfa RESV st c k NC24). cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).

  pose proof (@refill_tailK_x RNG R RESV k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.
  step. step. step.
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  -
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  -
    rewrite sx32_lit by (clear; lia).
    step. if_lit.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).
    step.
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End CANSECX.
End F_arefill_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module F_arefill.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition refill_entry := 0x42500.
End CANSEC1.
Notation REFILL_STACK := 672 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma v_divuw_lit : forall x y, 0 <= x < 2^31 -> 0 < y < 2^31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small x) by lia. f_equal.
  assert (B : 0 <= x / y <= x) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

Definition arec_hdr (L : alayout) (m : amem) (j cnt mc cs : Z) : Prop :=
  rw_cells bsegs m (acache_addr L j) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

End CANSEC2.
Ltac zfact := first [ split; zfact | vm_compute; first [reflexivity | discriminate | intros ?; discriminate] ].
Section CANSEC3. Context {rc : runConstT} {ov : annOV}.
Lemma mc_le4 : forall i, 1 <= i <= 4 -> max_cached i = 16 /\ 8 <= 1024 / (32 * i).
Proof.
  intros i Hi. assert (E : i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_mid : forall i, 5 <= i <= 16 -> max_cached i = 2 * (1024 / (32 * i)) /\ 1 <= 1024 / (32 * i) < 8.
Proof.
  intros i Hi. assert (E : i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_big : forall i, 17 <= i <= 30 -> max_cached i = 2 /\ 768 <= size_of_class i <= 65536 /\ 1024 / size_of_class i <= 1.
Proof.
  intros i Hi. assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_31 : max_cached 31 = 16. Proof. vm_compute. reflexivity. Qed.

Lemma size_formula2 : forall i, 17 <= i <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) = Z_to_bv 64 (size_of_class i).
Proof.
  intros i Hi.
  assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

Fixpoint ic_W (L : alayout) (i : Z) (d : nat) : list (Z * Z) :=
  match d with O => [] | Datatypes.S d' => (acache_addr L i + 4, acache_addr L i + 16) :: ic_W L (i + 1) d' end.

Lemma munch_cons_trans : forall p W m m1 m', munch [p] m m1 -> munch W m1 m' -> munch (p :: W) m m'.
Proof.
  intros [lo hi] W m m1 m' A B. eapply munch_trans; [eapply munch_weaken; [| exact A] | eapply munch_weaken; [| exact B]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; tauto.
Qed.

Lemma ic_W_disjoint_below : forall L i d A n, A + n <= acache_addr L i + 4 -> disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH. unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_gen : forall L i d A n, (A + n <= acache_addr L i + 4 \/ al_t L + 2768 <= A) -> i + Z.of_nat d <= 32 -> 1 <= i ->
  disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H Hd Hi; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_chunks : forall L i d c, disjoint_from (ic_W L i d) (acache_addr L c + 16) 64.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i c; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr; lia|]. apply IH.
Qed.

End CANSEC3.
Ltac icdj tac := cbn [disjoint_from cells_size csize Nat.add length]; split; [tac | first [apply ic_W_disjoint_chunks | apply ic_W_disjoint_gen; [tac | clear; cbn; lia | clear; lia]]].

Section CANSEC4. Context {rc : runConstT} {ov : annOV}.
Lemma ic_W_outside : forall L i d x, (x < acache_addr L i + 4 \/ al_t L + 2768 <= x) -> i + Z.of_nat d <= 32 -> 1 <= i -> outside (ic_W L i d) x.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i x Hx Hd Hi; cbn [ic_W outside]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma initcache_loop_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv bsegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  iclr (al_t L) 4096 ->
  evtF bsegs RNG (fun ms' => exists a1' a3' a5' t3' t4' t5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 a1' a2 a3' a4 a5' (Z_to_bv 64 15) (Z_to_bv 64 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x425f8) fc None m' (seg_rom bsegs)
      /\ munch (ic_W L i d) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x425a4) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT TIC; [lia|]. band_lin.
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t5x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells bsegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv bsegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono bsegs m mm ->
    evtF bsegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
               (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t5x t6)
          F (Z_to_bv 64 0x42580) fc None mm (seg_rom bsegs)))
  end.
  { intros q t5x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.
    setreg 29 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 13 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1 TIC; lia. }
      cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).
  {
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.
    step. step. step.
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 29 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).
  step.
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).
  -
    step.
    setreg 29 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  -
    do 7 zstep.
    setreg 28 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.
    setreg 29 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

Lemma max_cached_range : forall c, 1 <= c <= 31 -> 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
  intros c Hc. unfold max_cached.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.

Definition KKref {R} (k : astate -> bool -> AM R) (c n : Z) (st2 : astate) : AM R :=
  k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true.

Definition refill_tail_ret (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr bsegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = put_cls c (get_cls st2 c) st1)
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ (exists bfl : byte, rw_cells bsegs m' (RI + 68) [C1 bfl] /\ (c = K_BATCH_CLASS -> bfl = Z_to_bv 8 0))
  /\ rw_cells bsegs m' (RI + 72) [C8 stn']
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr bsegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma refill_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells bsegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42520) fc None m (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  set (n := max_cached c / 2) in *.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.
  step.
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  destruct GR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR & JR & GC2 & ST2E
                  & MU2 & WM2 & MI2 & ST2 & MTX2 & REG2 & EXH2 & STN2 & STATS2 & LSJ2 & STM2 & CH2 & AZU2 & AZF2 & MC2).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 271680)) with (Z_to_bv 64 271680 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exists (Z_to_bv 8 0); split; [exact EXH2| reflexivity]|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].
Qed.

Definition refill_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono bsegs m m1
  /\ refill_tail_ret L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Lemma init_cache_cinit : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma init_cache_cls : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma init_cache_space : forall st, a_space_beg (init_cache st) = a_space_beg st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma refill_tailK : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->

  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells bsegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x42520) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  assert (WOK1 : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).

  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.
  eapply (refill_tail_spec RNG k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  destruct TR as (_ & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & MUB & _ & _ & NC0 & _ & _ & NEWB & NEWM & _ & NLE & _ & _ & _ & _ & MUT & WMT & _).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  destruct B1 as (B1 & B2 & B3 & B4).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.

Lemma refill_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->

  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA RECS CXI TIC KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  rewrite cache_refill_tree_gfa. cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).

  pose proof (@refill_tailK RNG R k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.
  step. step. step.
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  -
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  -
    rewrite sx32_lit by (clear; lia).
    step. if_lit.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).
    step.
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End CANSEC4.
End F_arefill.

Module F_acdealloc.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom. Import F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition cdealloc_entry : Z := 0x3fd6c.
End CANSEC1.
Notation CDEALLOC_STACK := 688 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Lemma initcache_loop2_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a1 a2 a3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv bsegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  evtF bsegs RNG (fun ms' => exists a4' a5' a6' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 a4' a5' a6' (Z_to_bv 64 15)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4' t5' t6') F (Z_to_bv 64 0x3fef0) fc None m' (seg_rom bsegs)
      /\ munch (ic_W L i d) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6)
        F (Z_to_bv 64 0x3fe9c) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT; [lia|]. band_lin.
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t6x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells bsegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv bsegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono bsegs m mm ->
    evtF bsegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (acache_addr L i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t6x)
          F (Z_to_bv 64 0x3fe78) fc None mm (seg_rom bsegs)))
  end.
  { intros q t6x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.
    setreg 30 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.
    zstep.
    setreg 14 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1; lia. }
      cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).
  {
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.
    step. step. step.
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 30 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).
  step.
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).
  -
    step.
    setreg 30 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  -
    do 7 zstep.
    setreg 29 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.
    setreg 30 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

Definition cdmain_post (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sta' : word) m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
              (al_t L + 2784, al_t L + 2792)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 (k0 + 1)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)]
    /\ u32arr bsegs m' (acache_addr L c + 16) (upd chunks (Z.to_nat k0) (Z_to_bv 64 ((P - aregion L c) / 16)))
    /\ rw_cells bsegs m' (al_t L + 2784) [C8 sta'].

Lemma cd_main_spec : forall RNG (rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a5 a6 a7 s1x s2x s3x s4x t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (c k0 mc csz P lo : Z) (chunks : list word) (sta : word),
  stk bsegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 (al_space_beg L))] ->
  rw_cells bsegs m (acache_addr L c) [C4 (Z_to_bv 64 k0); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  u32arr bsegs m (acache_addr L c + 16) chunks -> length chunks = 16%nat ->
  rw_cells bsegs m (al_t L + 2784) [C8 sta] ->
  1 <= c < K_NUM_CLASSES -> 0 <= k0 < 16 -> 0 <= mc < 2^31 -> 0 <= csz < 2^63 ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  iclr (al_t L) 4096 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_t L) 4096 ->
  evtF bsegs RNG (cdmain_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc L c k0 mc csz P lo chunks m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1x
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) (Z_to_bv 64 P) (Z_to_bv 64 k0) a5 a6 a7
             s2x s3x s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3fdb0) fc None m (seg_rom bsegs)).
Proof.
  intros until sta. intros ST CEIL LO MI FR ISB CR CH LCH STA HC K0 MC CSZ P0 P1 SP1 SP2 T0 T1 TAL TI RIMG RSTK RT. band_lin.
  unfold AINSTANCE, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  word_range sp SPR.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (acache_addr L c + 16, acache_addr L c + 80);
                          (al_t L + 2784, al_t L + 2792)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  step.
  zstep. zstep. zstep. zstep. zstep.
  step.
  zstep. zstep. zstep. zstep. zstep.
  setreg 12 (Z_to_bv 64 (acache_addr L c + 4 * k0)) ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); rewrite Z.mod_small by (clear -K0; lia); f_equal;
      change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by (clear; lia); clear; lia).
  setreg 13 (Z_to_bv 64 ((P - aregion L c) / 16))
    ltac:(rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by (clear; lia); change (2^4) with 16; change (2^32) with 4294967296; f_equal; f_equal;
          rewrite RBE; rewrite (Z.mod_small (c * 4294967296)) by (clear -HC; lia);
          rewrite (Z.mod_small (P - c * 4294967296)) by (clear -HC P0 P1 SP1 SP2 RBE; lia);
          rewrite Z.mod_small by (clear -HC P0 P1 SP1 SP2 RBE; lia); clear; lia).
  box CH. box STA. box ISB.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  step.
  carry CH MUc WMc ltac:(rewrite LCH; clear; lia).
  carry STA MUc WMc ltac:(rewrite CAE; clear -HC; lia).
  carry ISB MUc WMc ltac:(rewrite CAE; clear -HC TI; lia).
  clear MUc WMc.
  pose proof (u32arr_store_ok bsegs _ (acache_addr L c + 16) _ k0 (wa (acache_addr L c + 16 + 4 * k0)) CH ltac:(rewrite LCH; clear -K0; lia) eq_refl) as SOK.
  box CR. box STA. box ISB. box FR.
  snapshot [(acache_addr L c + 16, acache_addr L c + 80)]%Z MUa WMa.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a (le4 ?v)) _) =>
    pose proof (u32arr_write bsegs mm (acache_addr L c + 16) _ k0 v CH ltac:(rewrite LCH; clear -K0; lia)) as CH2
  end.
  clear CH. store_done. try clear SOK.
  carry CR MUa WMa ltac:(clear; lia). carry STA MUa WMa ltac:(rewrite CAE; clear -HC; lia). carry ISB MUa WMa ltac:(rewrite CAE; clear -HC TI; lia).
  carry FR MUa WMa ltac:(rewrite CAE; clear -HC T1 SPR CEIL LO; lia). clear MUa WMa.
  zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2784)) = true) by (pose proof atop_range as AR; apply amo_alignedD_intro; [clear -TI T1 AR; lia| clear -TAL; Z.div_mod_to_equations; lia]).
  box CH2. box CR. box ISB.
  snapshot [(al_t L + 2784, al_t L + 2792)]%Z MUb WMb.
  amo_stepA AMO.
  carry CH2 MUb WMb ltac:(rewrite ?upd_length, LCH, CAE; clear -HC; lia). carry CR MUb WMb ltac:(rewrite CAE; clear -HC; lia). carry ISB MUb WMb ltac:(clear -TI; lia).
  clear MUb WMb.
  do 8 step.
  release_frame FR ST (bv_unsigned sp).
  unfold cdmain_post. finish.
  all: try eassumption.
Qed.

Lemma get_cls_init_cache : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma a_cinit_init_cache : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma max_count_init_cache : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite a_cinit_init_cache. reflexivity. Qed.
Lemma put_cls_put_cls : forall c x y st, put_cls c x (put_cls c y st) = put_cls c x st.
Proof. intros c x y st. unfold put_cls, set_cls. cbn. f_equal. rewrite insert_insert. destruct (decide (c = c)) as [|NE]; [reflexivity| exfalso; apply NE; reflexivity]. Qed.
Lemma get_cls_put_cls_same : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. apply get_cls_put_cls_eq. Qed.

Definition cd_W (L : alayout) (sp : Z) (c nf mfa mfa' : Z) : list (Z * Z) :=
  let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  ([(sp - 688, sp)] ++ ic_W L 1 31 ++
   [(CA, CA + 4); (CA + 16, CA + 80); (al_t L + 2784, al_t L + 2792); (al_t L + 2800, al_t L + 3168);
    (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
    (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)])%Z.

Definition cdealloc_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c P lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let CA := acache_addr L c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let mc := max_cached c in let half := mc / 2 in let cnt := c_count r in
  fp_le RNG RNG' /\
  exists (drained : bool) mfa' sj' (sta' : word),
  let nf' := if drained then nf + half else nf in
  let cnt' := if drained then cnt - half + 1 else cnt + 1 in

     drained = (a_cinit st && (cnt =? mc))%bool
  /\ get_cls stX c = mkAClass (c_mapped_user r) (c_allocated_user r) nf' mfa' cnt'
  /\ stX = put_cls c (get_cls stX c) (init_cache st)
  /\ (   mfa' = mfa
      \/ (drained = true /\ mfa < 4 * (nf + half) /\ mfa' = rup (4 * (nf + half)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf' <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0

  /\ munch (cd_W L (bv_unsigned sp) c nf mfa mfa') m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)

  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (c_count (get_cls st j)) (max_cached j) (size_of_class j))
  /\ arec_hdr L m' c cnt' (max_cached c) (size_of_class c)
  /\ u32arr bsegs m' (CA + 16) (upd chunks (Z.to_nat (cnt' - 1)) (Z_to_bv 64 ((P - aregion L c) / 16)))
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf'); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2784) [C8 sta']
  /\ (drained = true -> u32arr bsegs m' (FA + 4 * nf) (firstn (Z.to_nat half) (skipn (Z.to_nat (cnt - half)) chunks)))
  /\ junk_at m' (FA + 4 * nf') (mfa' - 4 * nf')
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma cdealloc_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c P lo : Z) (sj chunks : list word) (sta : word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CDEALLOC_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 P ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr bsegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells bsegs m (al_t L + 2784) [C8 sta] ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  aregion L c <= P -> P < aregion L c + K_REGION ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      cdealloc_ret L RNG sp st c P lo chunks m stX RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until sta. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF SBE HC CNTS NF MFA MFAM NFN P0 P1
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).
  pose proof atop_range as AR.
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, cdealloc_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCEV].
  pose proof (CNTS c ltac:(clear -HC; lia)) as CNTc. fold nf in CNTc.
  pose proof (RECS c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  box TCX. box SCX. box TSP.
  pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. clear CR.
  do 7 step.
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).

  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RECS0 : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
    [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MUN | exact WM |];
      cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -Hj SPR CEIL LO T0 T1; lia |]
  end.
  clear RECS.
  eapply junk_frame in J72; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia].
  eapply junk_frame in FJ; [| exact MUN | exact WM | intros _; cbn [disjoint_from]; rewrite FAE; clear -SPR CEIL LO SP1 SP2 HC NF MFA; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AZF0 : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC SPR CEIL LO MFA NF; Z.div_mod_to_equations; lia |];
    assert (MC0 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO; lia |]; apply Forall_nil |]
  end.
  clear AZF MC.
  pose proof (RECS0 c ltac:(clear -HC; lia)) as CR. unfold arec_hdr in CR.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (clear -HC; lia); clear -KZ HC; lia|].
  step. step. if_cases K32; zify_cond K32; [exfalso; rewrite ?unsigned_lit in K32 by (clear -HC; lia); clear -K32 HC; lia|].
  step. zstep. zstep.
  setreg 8 (Z_to_bv 64 (acache_addr L c)) ltac:(rewrite CAE; f_equal; clear; lia).
  step.
  unfold max_count in *.
  destruct (a_cinit st) eqn:CI.
  -
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step. if_cases KM; zify_cond KM; [exfalso; rewrite ?unsigned_lit in KM by (clear -MCR; lia); clear -KM MCR; lia|].
    step.
    rewrite (sx32_lit (c_count (get_cls st c))) by (clear -CNTc MCR; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -CNTc MCR; lia).
    +
      do 7 step.
      step.
      apply evtF_done.
      unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with true by (symmetry; apply Z.eqb_eq; exact KD).
      name_sp sp (-48).
      eapply cdrain_spec with (lo := lo) (L := L) (sj := sj) (chunks := chunks) (cnt := c_count (get_cls st c)) (mc := max_cached c) (csz := size_of_class c);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- m3_cells _ _ => exact MC0
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZF0
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              clear KONT; fold nf mfa; first [assumption | clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 CNTc KD MCR; lia]).

      intros st2 RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' DR.
      unfold cdrain_ret in DR. cbv zeta in DR. destruct DR as (md & MU01 & WM01 & RR & CR2 & CH2 & ST2).
      pose proof RR as RR0. unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP in RR0. cbv zeta in RR0. fold nf mfa in RR0.
      destruct RR0 as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & GC2 & ST2E & MU2 & WM2 & MI2 & _ & MTX2 & REG2 & J722 & STATS2 & LSJ2 & SRC2 & JR2 & AZF2 & MC2).
      rewrite Hsp in *. unname_sp.
      rewrite ?unsigned_lit in MU2 by (clear -SPR CEIL LO; lia).
      rewrite ?unsigned_lit in ST2 by (clear -SPR CEIL LO; lia).
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
      assert (SHF : shad (afreearr L c + mfa) + shlen (new - mfa) <= 0x10007fff8000).
      { rewrite !shad_div, !shlen_div, FAE. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE MCR. Z.div_mod_to_equations. lia. }
      assert (SHB2 : 2148262400 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).
      xport FR MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T1 HC; lia).
      xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      xport STA MU01 WM01 ltac:(rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      xport STA MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF MCR Y RIE FAE; lia).
      pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
      replace (ret_pc (Z_to_bv 64 261916)) with (Z_to_bv 64 261916 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      iprefix.
      step. step. step. step.
      step.
      rewrite (sx32_lit (c_count (get_cls st c) - max_cached c / 2)) by (clear -CNTc MCR KD; lia).
      step.
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST2
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 886328 _ => exact ISB2
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH2
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. cbv beta. eapply KONT.

      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa.
      split; [exact FPLE|].
      exists true, new, sj', sta'. cbn [andb].
      rewrite CI. cbn [andb].
      split; [symmetry; apply Z.eqb_eq; exact KD|].
      assert (GCX : get_cls (put_cls c (cls_set_count (c_count (get_cls st2 c) - max_cached c / 2 + 1)
                        (cls_set_num_freed (c_num_freed (get_cls st2 c) + max_cached c / 2) (get_cls st2 c))) st2) c
                    = mkAClass (c_mapped_user (get_cls st c)) (c_allocated_user (get_cls st c)) (nf + max_cached c / 2) new (c_count (get_cls st c) - max_cached c / 2 + 1)).
      { rewrite get_cls_put_cls_eq, GC2. reflexivity. }
      split; [exact GCX|].
      split. { rewrite GCX. unfold init_cache. rewrite CI. rewrite GC2. cbn [cls_set_count cls_set_num_freed c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count].
               destruct ST2E as [E|E]; rewrite E; [reflexivity|]. rewrite GC2, put_cls_put_cls. reflexivity. }
      split. { destruct UD as [E|(LT & E & FILL & R1 & R2 & BW)]; [left; exact E| right].
               split; [reflexivity|]. split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
               eapply fill_frame; [exact FILL | exact MU3 | exact WM3 |]. intros _. cbn [disjoint_from].
               clear -SPR CEIL LO SP1 SP2 HC T0 T0k SHB2 T1 NF MFA NEWB NEWGE SHF CAE. lia. }
      split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU01]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_trans; [eapply munch_weaken; [| exact MU2]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF NEWB NEWGE; lia). }
      split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM01| eapply wmono_trans; [exact WM2| exact WM3]]]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr.
               eapply cells_frame; [| exact MU3 | exact WM3 |].
               { eapply cells_frame; [| exact MU2 | exact WM2 |].
                 { eapply cells_frame; [exact (RECS0 j Hj) | exact MU01 | exact WM01 |].
                   cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
                 cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. ub TSP; clear -Hj NE SPR CEIL LO T0 T0k SHB2 T1 HC SP1 SP2 RIE FAE NF MFA NEWB SHF Y; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) - max_cached c / 2 + 1 - 1) with (c_count (get_cls st c) - max_cached c / 2) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG2 | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J722 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS2 | exact MU3 | exact WM3 | rewrite LSJ2; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ2|]. split; [exact STA3|].
      split. { intros _. eapply u32arr_frame; [exact SRC2 | exact MU3 | exact WM3 |]. rewrite length_firstn, length_skipn, LCH. cbn [disjoint_from]. rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR CNTc NFN; lia. }
      split; [eapply junk_frame; [exact JR2 | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MCR NEWB; lia]|].
      assert (SHF3 : 2148262400 <= shad (afreearr L c + new) /\ shad (afreearr L c + new) + shlen (536870912 - new) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF NEWB MCR AR; Z.div_mod_to_equations; lia).
      split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
    +
      pose proof MC0 as MC0'. destruct MC0' as (_ & _ & _ & _ & _ & _ & _ & ISB0 & _).
      pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
      eapply evtF_cut.
      { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks);
        try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- ATOP <= _ => atop_facts; exact CEIL
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
         | |- rw_cells _ _ 886328 _ => exact ISB0
         | |- rw_cells _ _ (acache_addr _ _) _ => exact CR
         | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
         | |- u32arr _ _ _ _ => exact CH
         | |- length _ = _ => exact LCH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
         | |- rng _ (al_t _) _ => exact RT
         | |- iclr _ _ => exact TIC
         end;
        unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
        first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
      cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
      apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. fold nf.
      replace (c_count (get_cls st c) =? max_cached c) with false by (symmetry; apply Z.eqb_neq; exact KD).
      eapply KONT.

      unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI. cbn [andb].
      split; [apply fp_le_refl|].
      exists false, mfa, sj, sta'.
      split; [symmetry; apply Z.eqb_neq; exact KD|].
      split; [rewrite get_cls_put_cls_eq; reflexivity|].
      split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
      split; [left; reflexivity|].
      split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
      split. { unfold cd_W. cbv zeta. cbn [ic_W app].
               eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
               eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
      split; [eapply wmono_trans; [exact WM| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|].
      split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS0 j Hj) | exact MU3 | exact WM3 |].
               cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
      split; [exact CR3|].
      split; [eapply u32arr_addr_eq; [replace (c_count (get_cls st c) + 1 - 1) with (c_count (get_cls st c)) by (clear; lia); exact CH3| reflexivity]|].
      split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
      split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
      split; [exact LSJ|]. split; [exact STA3|].
      split; [intros; discriminate|].
      split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
      assert (SHF3 : 2148262400 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
      split; [eapply azero_frame; [exact AZF0 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
      eapply m3_cells_frame; [exact MC0 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
  -
    replace (if false then max_cached c else 0) with 0 by reflexivity. rewrite (sx32_lit 0) by (clear; lia).
    assert (CNT0 : c_count (get_cls st c) = 0) by (clear -CNTc; lia).
    step. if_cases KM; zify_cond KM; [| exfalso; rewrite ?unsigned_lit in KM by (clear; lia); clear -KM; lia].
    do 9 step.
    setreg 14 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (32 * 1)) ltac:(f_equal; clear; lia).
    setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(f_equal; clear; lia).
    box FR. box STA. box CH. box MTX. box REG.
    eapply evtF_cut.
    { eapply (initcache_loop2_spec RNG 31 1 L (fun j => c_count (get_cls st j))); try reflexivity.
      - clear; lia.
      - intros j Hj. pose proof (RECS0 j Hj) as Rj. cbn in Rj. exact Rj.
      - assumption.
      - exact T0.
      - atop_facts; exact T1.
      - exact RT. }
    cbv beta. intros ms' (a4' & a5' & a6' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & RECS3).
    carry FR MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia]).
    carry STA MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    carry CH MU2 WM2 ltac:(rewrite LCH; apply ic_W_disjoint_chunks).
    carry MTX MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    carry REG MU2 WM2 ltac:(apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]).
    pose proof (stk_transport_disjoint bsegs _ _ m2 _ _ ST MU2 WM2 ltac:(apply ic_W_disjoint_gen; [right; clear -SPR CEIL LO T1; lia| clear; cbn; lia| clear; lia])) as ST2.
    eapply junk_frame in J72; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite RIE; unfold acache_addr; clear -SP1 SP2 HC Y; lia| clear; cbn; lia| clear; lia]].
    eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; apply ic_W_disjoint_gen; [ub TSP; rewrite FAE; unfold acache_addr; clear -SP1 SP2 HC Y NF MFA; lia| clear; cbn; lia| clear; lia]].
    xport STATS MU2 WM2 ltac:(rewrite LSJ; apply ic_W_disjoint_gen; [right; clear; lia| clear; cbn; lia| clear; lia]).
    assert (AZF2 : azero m2 (shad (afreearr L c + mfa)) (shlen (536870912 - mfa))).
    { eapply azero_frame; [exact AZF0 | exact MU2 | exact WM2 |]. intros _. assert (SHF3 : 2148262400 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
      apply ic_W_disjoint_gen; [unfold acache_addr; clear -SHF3 T0k; lia| clear; cbn; lia| clear; lia]. }
    assert (MC2 : m3_cells L m2).
    { eapply m3_cells_frame; [exact MC0 | exact MU2 | exact WM2 |]. unfold AIMG_HI, AIMG_LO. ub TCX. cbn [ic_W]. unfold acache_addr.
      repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC T0 T1 Y; lia |]). apply Forall_nil. }
    clear ST MI AZF0 MC0.
    pose proof (RECS3 c ltac:(clear -HC; lia)) as CR2. unfold arec_hdr in CR2. rewrite CNT0 in CR2.
    step.
    rewrite (sx32_lit (max_cached c)) by (clear -MCR; lia).
    step.
    rewrite (sx32_lit 0) by (clear; lia).
    step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by (clear -MCR; lia); [| exfalso; clear -KD MCR; lia].
    pose proof MC2 as MC2'. destruct MC2' as (_ & _ & _ & _ & _ & _ & _ & ISB2 & _).
    pose proof (size_of_class_facts c ltac:(unfold K_NUM_CLASSES; clear -HC; lia)) as [SZP SZ16].
    eapply evtF_cut.
    { eapply (cd_main_spec RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) with (lo := lo) (chunks := chunks) (k0 := 0);
      try lazymatch goal with
       | |- stk _ _ _ _ => exact ST2
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ 886328 _ => exact ISB2
       | |- rw_cells _ _ (acache_addr _ _) _ => exact CR2
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => exact LCH
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (al_t _) _ => exact RT
       | |- iclr _ _ => exact TIC
       end;
      unfold K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^32) with 4294967296; change (2^37) with 137438953472;
      first [assumption | clear -CNTc MCR KD HC SZP P0 P1 SP1 SP2 T0 T1 TAL LO; lia]. }
    cbv beta. intros ms' (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & sta' & m3 & -> & MU3 & WM3 & MI3 & ST3 & CR3 & CH3 & STA3).
    apply evtF_done. unfold cache_dealloc. cbv zeta. unfold init_cache, max_count. rewrite !CI. cbn [a_cinit set_cinit].
    change (get_cls (set_cinit true st) c) with (get_cls st c). fold nf. rewrite CNT0.
    replace (0 =? max_cached c) with false by (symmetry; apply Z.eqb_neq; clear -MCR; lia).
    eapply KONT.

    unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold nf mfa. rewrite CI, CNT0. cbn [andb].
    split; [apply fp_le_refl|].
    exists false, mfa, sj, sta'.
    split; [reflexivity|].
    split; [rewrite get_cls_put_cls_eq; reflexivity|].
    split; [rewrite get_cls_put_cls_eq; unfold init_cache; rewrite CI; reflexivity|].
    split; [left; reflexivity|].
    split; [clear -MFA; lia|]. split; [clear; lia|]. split; [exact MFAM|].
    split. { unfold cd_W. cbv zeta. cbn [ic_W app].
             eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]; cbn [ic_W]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia)|].
             eapply munch_weaken; [| exact MU3]; solve_sub_fpw ltac:(clear -SPR CEIL LO MFA NF; lia). }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { intros j Hj NE. unfold arec_hdr. eapply cells_frame; [exact (RECS3 j Hj) | exact MU3 | exact WM3 |].
             cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj NE SPR CEIL LO T0 T1 HC; lia. }
    split; [exact CR3|].
    split; [eapply u32arr_addr_eq; [exact CH3| reflexivity]|].
    split; [eapply cells_frame; [exact MTX | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply cells_frame; [exact REG | exact MU3 | exact WM3 | cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply junk_frame; [exact J72 | exact MU3 | exact WM3 | intros _; cbn; rewrite RIE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia]|].
    split; [eapply u64arr_frame; [exact STATS | exact MU3 | exact WM3 | rewrite LSJ; cbn; rewrite CAE; clear -SPR CEIL LO T0 T1 HC; lia]|].
    split; [exact LSJ|]. split; [exact STA3|].
    split; [intros; discriminate|].
    split; [eapply junk_frame; [exact FJ | exact MU3 | exact WM3 | intros _; cbn; rewrite FAE, CAE; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y NF MFA; lia]|].
    assert (SHF3 : 2148262400 <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 17594332446208)
        by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC NF MFA AR; Z.div_mod_to_equations; lia).
    split; [eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; rewrite CAE; clear -SPR CEIL LO SP1 SP2 HC T0k T1 SHF3; lia]|].
    eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. unfold AIMG_HI, AIMG_LO. rewrite CAE. ub TCX.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC T0 T1 HC Y; lia |]). apply Forall_nil.
Qed.
End CANSEC2.
End F_acdealloc.

Module F_arefill_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom_x. Import F_arefill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.

Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

Notation REFILL_STACK_X := 1504 (only parsing).

Section CANSECX. Context {rc : runConstT} {ov : annOV}.

Definition refill_tail_ret_x (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr bsegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = exh_clear c (put_cls c (get_cls st2 c) st1))
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st2 then 1 else 0))]
  /\ rw_cells bsegs m' (RI + 72) [C8 stn']
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr bsegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma refill_tail_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st1 then 1 else 0))] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells bsegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st1 m -> (let '(_, cap0, _) := a_emb st1 in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st1 in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st1 RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      xfalse_ret L RESV RNG sp REFILL_STACK_X st1 c lo m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret_x L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree_x RESV st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42520) fc None m (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  set (n := max_cached c / 2) in *.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  zstep.
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.
  step.
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec_x with (lo := lo) (L := L) (RESV := RESV);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELRO
       | |- exh_cells _ => exact XC | |- emb_cells _ _ => exact EC | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG
       | |- bv_unsigned _ < 2 ^ 63 => rewrite Hsp; pose proof atop_range; clear -SP63 SPR CEIL LO; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  1: {
    intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' XF.
    unfold xfalse_ret in XF. cbv zeta in XF.
    destruct (a_emb st1) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct XF as (FPLE & STREL & EC2 & ERNG2 & XC2 & MTX2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    unname_sp. pose proof atop_range as ATR.
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK.
    assert (RIHI : aregion_info L c + 128 <= ATOP).
    { unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. clear -SP2 HC. lia. }
    assert (B0 : cap0 = 0 \/ (0 < cap0 /\ d0 + cap0 <= ATOP)) by (destruct (emb_cells_top st1 m d0 cap0 sz0 EC EE) as [Z0|(CP0 & _ & TB0)]; [left| right; split]; assumption).
    assert (B2 : cap2 = 0 \/ (0 < cap2 /\ d2 + cap2 <= ATOP)) by (destruct (emb_cells_top st2 m2 d2 cap2 sz2 EC2 EE2) as [Z2|(CP2 & _ & TB2)]; [left| right; split]; assumption).
    eapply (cells_frameO _ _ m2) in FR; [| exact MU2 |
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; intros x Hx; cbn [outside]; unfold AEMB;
      repeat split; try exact I; clear -Hx SPR LO CEIL RIHI ATR B0 B2 TP1; lia].
    replace (ret_pc (Z_to_bv 64 271680)) with (Z_to_bv 64 271680 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    iprefix.
    step. if_lit.
    lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
    refresh RSTK. do 5 step.
    lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    subst PP. apply evtF_done. eapply KF.
    unfold xfalse_ret. cbv zeta. rewrite EE, EE2.
    split; [exact FPLE|]. split; [exact STREL|]. split; [exact EC2|]. split; [exact ERNG2|]. split; [exact XC2|]. split; [exact MTX2|]. split; [exact FLG2|].
    split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TP1]]].
             eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    split; [exact MI2| assumption]. }

  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  destruct GR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR & JR & GC2 & ST2E
                  & MU2 & WM2 & MI2 & ST2 & MTX2 & REG2 & EXH2 & STN2 & STATS2 & LSJ2 & STM2 & CH2 & AZU2 & AZF2 & MC2).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 271680)) with (Z_to_bv 64 271680 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].
Qed.

Definition refill_ret_x (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono bsegs m m1
  /\ refill_tail_ret_x L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Definition refill_ret_false (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo cntc : Z) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK_X, bv_unsigned sp) :: ic_W L 1 31)%Z m m1
  /\ xfalse_ret L RESV RNG sp REFILL_STACK_X (init_cache st) c lo m1 st2 RNG' m'
  /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 (size_of_class c))]
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Definition cache_refill_tree_x {R} (RESV : list (Z * Z)) (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array_x ATOP RESV st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).
Lemma cache_alloc_x_unfold : forall {R} RESV st c (k : astate -> bool -> AM R),
  cache_alloc_x ATOP RESV st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree_x RESV st c k).
Proof. intros. reflexivity. Qed.
Lemma cache_refill_tree_x_gfa : forall {R} RESV st c (k : astate -> bool -> AM R), c <> K_BATCH_CLASS ->
  cache_refill_tree_x RESV st c k =
  (let st1 := init_cache st in let n := max_count st1 c / 2 in
   gfa_tree_x RESV st1 c n k (fun st2 => k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true)).
Proof.
  intros R RESV st c k NC. unfold cache_refill_tree_x, gfa_tree_x, gfa_take, populate_free_array_x. cbv zeta.
  replace (c =? K_BATCH_CLASS) with false by (symmetry; apply Z.eqb_neq; exact NC). reflexivity.
Qed.

Lemma refill_tailK_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->
  pcov RESV (al_t L) (al_t L + 4096) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_false L RESV RNG sp st c lo cntc cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->

  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells bsegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree_x RESV st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x42520) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG TRES TOLD KF KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  assert (WOK1 : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).

  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.

  pose proof atop_range as ATR.
  assert (IC1 : img_clear ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { apply img_clear_band. eapply Forall_impl; [| exact WOK1]. cbv beta. intros iv [X _]. exact X. }
  assert (EE1 : a_emb st1 = a_emb st) by (rewrite E1; apply init_cache_emb).
  assert (XM1 : exh_mem c st1 = exh_mem c st) by (rewrite E1; apply init_cache_exh).
  assert (RELRO1 : arelro m1) by (exact (arelro_frameO m m1 _ RELRO MU1 IC1)).
  assert (XC1 : exh_cells m1) by (exact (exh_cells_frameO m m1 _ XC MU1 IC1)).
  assert (EC1 : emb_cells st1 m1).
  { assert (X : emb_cells st m1).
    { apply (emb_cells_frameO st m m1 _ EC MU1 IC1). destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE0.
      destruct (emb_cells_top st m d0 cap0 sz0 EC EE0) as [Z0|(CP0 & _ & TB0)]; [intros x Hx; exfalso; clear -Z0 Hx; lia|].
      intros x Hx. cbn [outside]. split; [clear -Hx TB0 LO CEIL; lia|].
      apply ic_W_outside; [unfold acache_addr; clear -Hx TOLD CP0; lia| clear; cbn; lia| clear; lia]. }
    unfold emb_cells in *. rewrite EE1. exact X. }
  rewrite <- EE1 in CAPB, RIOLD. rewrite <- XM1 in EXH.
  assert (ERNG1 : emb_rng st1 RNG) by (unfold emb_rng in *; rewrite EE1; exact ERNG).
  eapply (refill_tail_spec_x RNG RESV k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- exh_first_stmt => exact EXHW | |- aresv_ok _ _ => exact ROK | |- arelro _ => exact RELRO1
       | |- exh_cells _ => exact XC1 | |- emb_cells _ _ => exact EC1 | |- pcov _ _ _ => exact RIRES | |- emb_rng _ _ => exact ERNG1
       | |- bv_unsigned _ < 2 ^ 63 => exact SP63
       | |- bv_unsigned _ < 32 => exact FC
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).

  1: {
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' XF. eapply KF. exists m1.
    split; [eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; intros x [OA OB]; split; [clear -OA; lia| exact OB]|]. split; [rewrite <- E1; exact XF|].
    unfold xfalse_ret in XF. cbv zeta in XF. destruct (a_emb st1) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
    destruct XF as (FPLE & STREL & EC2 & ERNG2 & XC2 & MTX2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TP1) & MI2 & ST2).
    rewrite <- EE1 in TOLD. cbv beta iota in TOLD.
    assert (CLT : forall d cap, emb_prov RESV st1 d0 cap0 d cap -> cap <= 0 \/ al_t L + 4096 <= d \/ d + cap <= al_t L).
    { intros d cap [(-> & ->)|AV]; [clear -TOLD; lia|].
      destruct (Z_le_gt_dec cap 0) as [LE0|GT0]; [left; exact LE0| right].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      pose proof (pcov_clear _ _ _ _ _ TRES AV ltac:(clear; lia) ltac:(clear -GT0; lia)) as C. clear -C. lia. }
    pose proof (CLT d1 cap1 PV1) as CL1. pose proof (CLT d2 cap2 PV2) as CL2.
    assert (REC_T : forall j cs, 1 <= j <= 31 -> rw_cells bsegs m1 (acache_addr L j) cs -> Z.of_nat (cells_size cs) = 16 -> rw_cells bsegs m' (acache_addr L j) cs).
    { intros j cs Hj RC SZ. eapply cells_frameO; [exact RC| exact MU2|]. rewrite SZ. intros x Hx. cbn [outside]. unfold AEMB, acache_addr in *.
      ub TSP. rewrite RIE. repeat split; try exact I; clear -Hx Hj SPR CEIL LO SP1 SP2 HC T0 T1 TIC TB Y TOLD CL1 CL2 ATR; lia. }
    split; [apply (REC_T c _ ltac:(clear -HC; lia) REC1 eq_refl)|].
    intros j Hj Hjc. unfold arec_hdr. apply (REC_T j _ Hj (RECS1 j Hj Hjc) eq_refl). }

  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret_x, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  destruct TR as (_ & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & MUB & _ & _ & NC0 & _ & _ & NEWB & NEWM & _ & NLE & _ & _ & _ & _ & MUT & WMT & _).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  destruct B1 as (B1 & B2 & B3 & B4).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.

Lemma refill_spec_x : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  c <> K_BATCH_CLASS ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK_X ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->

  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->
  pcov RESV (al_t L) (al_t L + 4096) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_false L RESV RNG sp st c lo (cnt c) cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree_x RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros NC24 ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA RECS CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG TRES TOLD KF KONT. band_lin.
  pose proof T0 as TB. unfold sclr, KLS in TB.
  rewrite (cache_refill_tree_x_gfa RESV st c k NC24). cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).

  pose proof (@refill_tailK_x RNG R RESV k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.
  step. step. step.
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  -
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  -
    rewrite sx32_lit by (clear; lia).
    step. if_lit.
    zstep.
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).
    step.
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End CANSECX.
End F_arefill_x.
End TwinB.
