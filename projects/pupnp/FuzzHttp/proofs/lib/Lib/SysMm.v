(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ITree Ceiling Nodes SysStep Decode.
Import ListNotations.
Open Scope bv_scope.

Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_nonneg : forall len, (0 <= len)%Z -> (0 <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_lt : forall len, (mmap_len len < len + 4096)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Definition munmap_ret (a : range_ans) : word :=
  match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
  match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
  intros Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
  if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
  else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].

Lemma alloc_ceiling_max_val : alloc_ceiling_max = 0x7fffff800000%Z.
Proof. reflexivity. Qed.
Lemma alloc_floor_val : alloc_floor = 0x7fff7f800000%Z.
Proof. reflexivity. Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Ltac sys_nret_raw :=
  (try (lazymatch goal with
        | |- evt _ _ (nret _ ?rsp) =>
            match goal with
            | Hs : strip rsp = ?e |- _ => apply evt_nret_strip; rewrite Hs
            | Hs : ?e = strip rsp |- _ => apply evt_nret_strip; rewrite <- Hs
            end
        end));
  unfold efferr, eff0;
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].

Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

Section Copy.
Variables (segs : list Segment) (before m : word -> option byte) (src dst len : Z).
Hypothesis Hdst : (0 <= dst < 2^64)%Z.
Hypothesis Hlen : (0 <= len < 2^64)%Z.
Hypothesis Hdl : (dst + len <= 2^64)%Z.
Let c := mkCopy (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 len).
Let m' := apply_copy before m c.

#[using="Hdst Hlen"] Lemma copy_outside : forall x, (bv_unsigned x < dst \/ dst + len <= bv_unsigned x)%Z -> m' x = m x.
Proof.
  intros x Hx. unfold m', apply_copy, c. cbn [copy_dst copy_len copy_src]. rewrite !unsigned_lit by lia.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + len)); cbn [andb]; try reflexivity. lia.
Qed.

#[using="Hdst Hlen"] Lemma bytes_at_copy_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= dst \/ dst + len <= A)%Z -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite copy_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Hdst Hlen"] Lemma wr_at_copy_other : forall A k,
  wr_at segs m A k -> (A + k <= dst \/ dst + len <= A)%Z -> wr_at segs m' A k.
Proof.
  intros A k (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite copy_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

#[using="Hdst Hlen"] Lemma rw_cells_copy_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= dst \/ dst + len <= A)%Z -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
  - apply bytes_at_copy_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
  - apply wr_at_copy_other; [exact Hw| exact Hd].
Qed.

#[using="Hdst Hlen"] Lemma stk_copy_other : forall lo hi, stk segs m lo hi -> (hi <= dst \/ dst + len <= lo)%Z -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H) Hd. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  assert (E : m' (wa x) = m (wa x)). { apply copy_outside. rewrite wa_unsigned by lia. lia. }
  split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Hdst Hlen"] Lemma munch_copy : forall W m0, munch W m0 m -> inside W dst len -> munch W m0 m'.
Proof.
  intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
  rewrite copy_outside. { apply H. exact Hx. }
  destruct (Z.ltb_spec0 (bv_unsigned x) dst); [lia|].
  destruct (Z.leb_spec0 (dst + len) (bv_unsigned x)); [lia|].
  exfalso. eapply (inside_not_outside W dst len (bv_unsigned x) Hin); [lia| exact Hx].
Qed.

#[using="Hdst Hlen"] Lemma mem_inv_copy : mem_inv segs m -> (forall x : word, (dst <= bv_unsigned x < dst + len)%Z -> ro_addr segs x = false) ->
  mem_inv segs m'.
Proof.
  intros Hinv Hro x b Hx. pose proof (bv_unsigned_in_range 64 x).
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + len)).
  1: apply Hro; lia.
  all: rewrite copy_outside in Hx by lia; exact (Hinv _ _ Hx).
Qed.
End Copy.
