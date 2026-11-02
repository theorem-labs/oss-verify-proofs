(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP05.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Record xchunk := mkX { x_addr : sv; x_val : cval }.
Record xzone := mkXZ { xz_base : sv; xz_elt : Z; xz_count : sv }.
Record xstate := mkXS { xs_ss : sstate; xs_chunks : list xchunk; xs_zones : list xzone; xs_dirty : list (sv * Z) }.
Definition x_len (c : xchunk) : Z := cv_len (x_val c).
Definition lin_diff (a b : sv) : option Z :=
if sv_eqb a b then Some 0 else
match lin_nf a, lin_nf b with
| Some (la, ca), Some (lb, cb) => if lin_eqb la lb then Some (ca - cb) else None
| _, _ => None
end.
Fixpoint xfind (xs : list xchunk) (a : sv) (n : Z) : option (xchunk * Z) :=
match xs with
| [] => None
| c :: r =>
match lin_diff a (x_addr c) with
| Some k => if (0 <=? k) && (k + n <=? x_len c) then Some (c, k) else xfind r a n
| None => xfind r a n
end
end.
Section g.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Definition xload (G : facts) (xs : list xchunk) (a : sv) (sz : msize) (sg : bool) : option sv :=
match xfind xs a (Z.of_nat (nbytes sz)) with
| None => None
| Some (c, k) =>
match x_val c with
| CVal w v =>
if negb (Z.of_N w <=? 8) then None
else if k =? 0 then Some (loadres G sz sg v)
else Some (loadres G sz sg (s_alu G ALU_SRL v (SLit (8 * k))))
| CZero _ => Some (SLit 0)
| CImg _ => None
| CData d s _ => if 0 <=? s then Some (loadres G sz sg (SData d (s + k) (N.of_nat (nbytes sz)))) else None
end
end.
Definition idx_lt_count (G : facts) (idx count : sv) : bool :=
cond_assumed (f_conds G) BC_LTU idx count
|| match itv_lt (sv_urange G idx) (sv_urange G count) with Some true => true | _ => false end.
Definition zone_elem (z : xzone) (idx : sv) : sv :=
SAlu ALU_ADD (xz_base z) (SMd M_MUL idx (SLit (xz_elt z))).
Fixpoint zone_find_idx (G : facts) (cs : list acond) (z : xzone) (a : sv) (n : Z) : option (sv * Z) :=
match cs with
| [] => None
| mkAC BC_LTU idx cnt :: r =>
if sv_eqb cnt (xz_count z) then
match lin_diff a (zone_elem z idx) with
| Some k => if (0 <=? k) && (k + n <=? xz_elt z) then Some (idx, k)
else zone_find_idx G r z a n
| None => zone_find_idx G r z a n
end
else zone_find_idx G r z a n
| _ :: r => zone_find_idx G r z a n
end.
Fixpoint zone_find (G : facts) (zs : list xzone) (a : sv) (n : Z) : option (xzone * sv * Z) :=
match zs with
| [] => None
| z :: r =>
match zone_find_idx G (f_conds G) z a n with
| Some (idx, k) => Some (z, idx, k)
| None => zone_find G r a n
end
end.
Definition two_idx (l : lin) : option (nat * nat * Z) :=
match l with
| [(x, cx); (y, cy)] =>
if (0 <? cy) && (cx =? - cy) then Some (x, y, cy)
else if (0 <? cx) && (cy =? - cx) then Some (y, x, cx) else None
| _ => None
end.
Definition atom_lt (G : facts) (i j : nat) : bool :=
cond_assumed (f_conds G) BC_LTU (SOff i 0) (SOff j 0)
|| match itv_lt (sv_urange G (SOff i 0)) (sv_urange G (SOff j 0)) with Some true => true | _ => false end.
Definition xsep_idx (G : facts) (a : sv) (n : Z) (c : xchunk) : bool :=
match lin_nf a, lin_nf (x_addr c), sv_urange G a, sv_urange G (x_addr c) with
| Some (la, ka), Some (lc, kc), Some (al, ah), Some (cl, ch) =>
match two_idx (lin_clean (lin_merge lc (lin_scale (-1) la))) with
| Some (i, j, m) =>
let d := kc - ka in
match sv_urange G (SOff i 0), sv_urange G (SOff j 0) with
| Some (_, ih), Some (_, jh) =>
(atom_lt G i j && (n <=? m + d) && (ah + m * jh + d <? M64))
|| (atom_lt G j i && (d + x_len c <=? m) && (ch + m * ih <? al + d + M64))
| _, _ => false
end
| None => false
end
| _, _, _, _ => false
end.
Definition xsep_itv (G : facts) (a : sv) (n : Z) (c : xchunk) : bool :=
match sv_urange G a, sv_urange G (x_addr c) with
| Some (al, ah), Some (cl, ch) =>
(ah + n <=? cl) || (ch + x_len c <=? al) ||
match lin_diff (x_addr c) a with
| Some d => ((n <=? d) && (ah + d <? M64)) || ((d + x_len c <=? 0) && (0 <=? al + d))
| None => false
end
| _, _ => false
end.
Definition xsep (G : facts) (a : sv) (n : Z) (c : xchunk) : bool :=
xsep_itv G a n c || xsep_idx G a n c.
Definition xfilter (G : facts) (a : sv) (n : Z) (xs : list xchunk) : list xchunk :=
List.filter (xsep G a n) xs.
Inductive xres :=
| XRun (xs : xstate)
| XEcall (xs : xstate)
| XStop (why : stop_reason).
Definition xwith (xs : xstate) (ss : sstate) (cs : list xchunk) : xstate :=
mkXS ss cs (xs_zones xs) (xs_dirty xs).
Definition xsym_step (xs : xstate) : xres :=
let ss := xs_ss xs in
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
match clookup tbl (ss_pc ss) with
| None => XStop SR_fetch
| Some wz =>
let w := Z_to_bv 32 wz in
if is_ecall w then match sym_step segs tbl ss with SEcall ss' => XEcall (xwith xs ss' (xs_chunks xs)) | _ => XStop SR_unsupported end else
match decode_any w with
| None => XStop SR_decode
| Some (i, isz) =>
if negb (isz =? 4) then XStop SR_unsupported else
match i with
| Load sz sg rd rs1 imm =>
match sym_step segs tbl ss with
| SRun ss' => XRun (xwith xs ss' (xs_chunks xs))
| SEcall _ => XStop SR_unsupported
| SStop why =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match xload G (xs_chunks xs) a sz sg with
| Some v => XRun (xwith xs (setreg ss rd v (ss_pc ss + 4)) (xs_chunks xs))
| None => XStop why
end
end
| Store sz rs1 rs2 imm =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
let n := Z.of_nat (nbytes sz) in
match sym_step segs tbl ss with
| SRun ss' => XRun (xwith xs ss' (xfilter G a n (xs_chunks xs)))
| SEcall _ => XStop SR_unsupported
| SStop why =>
match ss_resv ss with
| Some _ => XStop SR_resv
| None =>
match zone_find G (xs_zones xs) a n with
| None => XStop why
| Some _ =>
XRun (mkXS (mkSST (ss_pc ss + 4) (ss_regs ss) (ss_fregs ss) (ss_mem ss) None G)
(mkX a (CVal (N.of_nat (nbytes sz)) (R rs2)) :: xfilter G a n (xs_chunks xs))
(xs_zones xs) ((a, n) :: xs_dirty xs))
end
end
end
| Sc wd _ _ rd rs1 rs2 =>
match sym_step segs tbl ss with
| SRun ss' => XRun (xwith xs ss' (xfilter G (R rs1) (amo_bytes_of wd) (xs_chunks xs)))
| SEcall _ => XStop SR_unsupported
| SStop why => XStop why
end
| _ =>
match sym_step segs tbl ss with
| SRun ss' => XRun (xwith xs ss' (xs_chunks xs))
| SEcall ss' => XEcall (xwith xs ss' (xs_chunks xs))
| SStop why => XStop why
end
end
end
end.
Inductive xrun_status := XS_running | XS_ecall | XS_stopped (why : stop_reason).
Fixpoint xsym_run (fuel : nat) (xs : xstate) : xstate * xrun_status :=
match fuel with
| O => (xs, XS_running)
| S f => match xsym_step xs with
| XRun xs' => xsym_run f xs'
| XEcall xs' => (xs', XS_ecall)
| XStop why => (xs, XS_stopped why)
end
end.
Fixpoint xsym_run_to (fuel : nat) (stop : Z) (xs : xstate) : xstate * xrun_status :=
match fuel with
| O => (xs, XS_running)
| S f => if ss_pc (xs_ss xs) =? stop then (xs, XS_running) else
match xsym_step xs with
| XRun xs' => xsym_run_to f stop xs'
| XEcall xs' => (xs', XS_ecall)
| XStop why => (xs, XS_stopped why)
end
end.
Definition clear_dirty (xs : xstate) : xstate := mkXS (xs_ss xs) (xs_chunks xs) (xs_zones xs) [].
Definition xsym_runN (n : N) (xs : xstate) := xsym_run (N.to_nat n) (clear_dirty xs).
Definition xsym_run_toN (n : N) (stop : Z) (xs : xstate) := xsym_run_to (N.to_nat n) stop (clear_dirty xs).
Fixpoint xsym_run_tos (fuel : nat) (stops : list Z) (xs : xstate) : xstate * xrun_status :=
match fuel with
| O => (xs, XS_running)
| S f => match xsym_step xs with
| XRun xs' => if existsb (Z.eqb (ss_pc (xs_ss xs'))) stops then (xs', XS_running)
else xsym_run_tos f stops xs'
| XEcall xs' => (xs', XS_ecall)
| XStop why => (xs, XS_stopped why)
end
end.
Definition xsym_run_tosN (n : N) (stops : list Z) (xs : xstate) := xsym_run_tos (N.to_nat n) stops (clear_dirty xs).
Definition zone_lo (E : env) (z : xzone) : Z := bv_unsigned (sv_denot E (xz_base z)).
Definition zone_hi (E : env) (z : xzone) : Z :=
zone_lo E z + xz_elt z * bv_unsigned (sv_denot E (xz_count z)).
Definition in_zone (E : env) (z : xzone) (x : Z) : Prop := zone_lo E z <= x < zone_hi E z.
Definition xchunk_ok (E : env) (m : word -> option byte) (zs : list xzone) (c : xchunk) : Prop :=
let A := bv_unsigned (sv_denot E (x_addr c)) in
0 <= x_len c /\ A + x_len c <= 2 ^ 64
/\ chunk_ok segs E m A (mkChunk 0 (x_val c))
/\ match x_val c with CImg _ => False | _ => True end
/\ exists z, In z zs /\ zone_lo E z <= A /\ A + x_len c <= zone_hi E z.
Definition xzone_ok (E : env) (m : word -> option byte) (rs : smem) (z : xzone) : Prop :=
0 < xz_elt z < M64 /\ zone_hi E z < 2 ^ 64
/\ (forall x, in_zone E z x -> m (Z_to_bv 64 x) <> None)
/\ (forall b lo hi wlo whi x, In (b, lo, hi, wlo, whi) (skeleton rs) -> in_zone E z x ->
~ (base_val E b + lo <= x < base_val E b + hi)).
Definition xmem_ok (E : env) (m : word -> option byte) (rs : smem) (cs : list xchunk) (zs : list xzone) : Prop :=
Forall (xchunk_ok E m zs) cs /\ Forall (xzone_ok E m rs) zs.
Definition xst_ok (E : env) (xs : xstate) (ms : machine_state) : Prop :=
st_ok segs E (xs_ss xs) ms
/\ xmem_ok E (ms_mem ms) (ss_mem (xs_ss xs)) (xs_chunks xs) (xs_zones xs).
Definition xst_ok_ecall (E : env) (xs : xstate) (ms : machine_state) : Prop :=
st_ok_ecall segs E (xs_ss xs) ms
/\ xmem_ok E (ms_mem ms) (ss_mem (xs_ss xs)) (xs_chunks xs) (xs_zones xs).
Definition in_zones (E : env) (zs : list xzone) (x : Z) : Prop :=
exists z, In z zs /\ in_zone E z x.
Definition in_dirty (E : env) (d : list (sv * Z)) (x : Z) : Prop :=
exists a n, In (a, n) d /\ bv_unsigned (sv_denot E a) <= x < bv_unsigned (sv_denot E a) + n.
Lemma in_dirty_mono : forall E d d' x, (forall e, In e d -> In e d') -> in_dirty E d x -> in_dirty E d' x.
Proof. intros E d d' x Hsub (a & n & Hin & Hx). exists a, n. auto. Qed.
Definition xframe (E : env) (rs : smem) (d : list (sv * Z)) (m m' : word -> option byte) : Prop :=
forall x : word, ~ in_wrange E rs (bv_unsigned x) -> ~ in_dirty E d (bv_unsigned x) -> m' x = m x.
Lemma xframe_refl : forall E rs d m, xframe E rs d m m.
Proof. intros E rs d m x _ _. reflexivity. Qed.
Lemma xframe_mono : forall E rs d d' m m',
(forall e, In e d -> In e d') -> xframe E rs d m m' -> xframe E rs d' m m'.
Proof. intros E rs d d' m m' Hsub H x Hw Hd. apply H; [exact Hw|]. intros Hin. apply Hd. eapply in_dirty_mono; eauto. Qed.
Lemma xframe_trans : forall E rs rs' d m1 m2 m3,
skeleton rs = skeleton rs' ->
xframe E rs d m1 m2 -> xframe E rs' d m2 m3 -> xframe E rs d m1 m3.
Proof.
intros E rs rs' d m1 m2 m3 Hsk H12 H23 x Hw Hz.
rewrite (H23 x); [apply H12; assumption| |exact Hz].
intros Hin. apply Hw. eapply in_wrange_skeleton; [symmetry; exact Hsk| exact Hin].
Qed.
Lemma frame_xframe : forall E rs d m m', frame_of E rs m m' -> xframe E rs d m m'.
Proof. intros E rs d m m' H x Hw _. apply H. exact Hw. Qed.
Lemma lin_diff_sound : forall E a b k,
lin_diff a b = Some k -> U E a = (U E b + k) mod M64.
Proof.
intros E a b k H. unfold lin_diff in H.
destruct (sv_eqb a b) eqn:Heq.
{ injection H as <-. apply sv_eqb_eq in Heq. subst. rewrite Z.add_0_r.
pose proof (U_range E b). symmetry. apply Z.mod_small. lia. }
destruct (lin_nf a) as [[la ca]|] eqn:Ha; [|discriminate].
destruct (lin_nf b) as [[lb cb]|] eqn:Hb; [|discriminate].
destruct (lin_eqb la lb) eqn:Hl; [|discriminate]. injection H as <-.
apply lin_eqb_eq in Hl. subst lb.
rewrite (lin_nf_sound E a la ca Ha), (lin_nf_sound E b la cb Hb).
unfold M64. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
Lemma lin_diff_exact : forall E a b k,
lin_diff a b = Some k -> 0 <= U E b + k < M64 -> U E a = U E b + k.
Proof.
intros E a b k H Hr. rewrite (lin_diff_sound E a b k H). apply Z.mod_small. lia.
Qed.
Lemma xfind_sound : forall xs a n c k,
xfind xs a n = Some (c, k) -> In c xs /\ lin_diff a (x_addr c) = Some k /\ 0 <= k /\ k + n <= x_len c.
Proof.
induction xs as [|c0 r IH]; cbn; intros a n c k H; [discriminate|].
destruct (lin_diff a (x_addr c0)) as [k0|] eqn:Hd.
- destruct ((0 <=? k0) && (k0 + n <=? x_len c0)) eqn:Hc.
+ injection H as <- <-. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. auto.
+ destruct (IH a n c k H) as (Hin & Hd' & Hk). auto.
- destruct (IH a n c k H) as (Hin & Hd' & Hk). auto.
Qed.
Lemma xload_sound : forall E G m zs xs a sz sg v,
facts_ok E G -> Forall (xchunk_ok E m zs) xs ->
xload G xs a sz sg = Some v ->
exists bs, rdn segs m (sv_denot E a) (nbytes sz) = Some bs /\
sv_denot E v = load_result sz sg (le_bytes_to_word bs).
Proof.
intros E G m zs xs a sz sg v HG Hxs H. unfold xload in H.
destruct (xfind xs a (Z.of_nat (nbytes sz))) as [[c k]|] eqn:Hf; [|discriminate].
apply xfind_sound in Hf as (Hin & Hd & Hk0 & Hkn).
rewrite Forall_forall in Hxs. pose proof (Hxs c Hin) as (Hlen & Hnw & Hc & Hnimg & Hz).
pose proof (u64_range (sv_denot E (x_addr c))) as HA.
pose proof (nbytes_pos sz) as Hn.
assert (HUa : bv_unsigned (sv_denot E a) = bv_unsigned (sv_denot E (x_addr c)) + k).
{ change (U E a = U E (x_addr c) + k). apply (lin_diff_exact E a (x_addr c) k Hd). unfold U, M64. lia. }
remember (bv_unsigned (sv_denot E (x_addr c))) as A eqn:HeqA.
assert (Hav : sv_denot E a = Z_to_bv 64 (A + k)).
{ rewrite <- HUa. symmetry. apply lit_of_word. }
rewrite Hav.
destruct (x_val c) as [w cv | len | len | d s0 len] eqn:Hcv; try contradiction.
-
destruct (Z.of_N w <=? 8) eqn:Hw8; cbn [negb] in H; [|discriminate]. apply Z.leb_le in Hw8.
set (u := bv_unsigned (sv_denot E cv)).
exists (zbytes u k (nbytes sz)). split.
+ rewrite zbytes_as_map. replace (A + k) with (A + (0 + k)) by lia.
eapply (chunk_read segs E m A (mkChunk 0 (CVal w cv)) (0 + k)); [exact Hc | cbn; lia | cbn; unfold x_len in Hkn; rewrite Hcv in Hkn; cbn in Hkn; lia |].
intros i Hi. cbn [cbyte c_off c_val]. unfold byte_of_word. f_equal. f_equal. f_equal. lia.
+ rewrite le_bytes_to_word_Z, zbytes_spec by (subst u; pose proof (u64_range (sv_denot E cv)); lia).
destruct (k =? 0) eqn:Hk.
* injection H as <-. apply Z.eqb_eq in Hk. rewrite Hk, Z.mul_0_r, Z.shiftr_0_r.
apply (loadres_sound E G sz sg cv u HG). subst u. symmetry. apply lit_of_word.
* injection H as <-. apply Z.eqb_neq in Hk.
assert (Hkw : k + Z.of_nat (nbytes sz) <= Z.of_N w).
{ unfold x_len in Hkn. rewrite Hcv in Hkn. cbn [cv_len] in Hkn. lia. }
apply (loadres_sound E G sz sg _ _ HG). apply (srl_lit_small E G cv u k HG eq_refl); lia.
-
injection H as <-. exists (repeat (Z_to_bv 8 0) (nbytes sz)). split.
+ replace (repeat (Z_to_bv 8 0) (nbytes sz)) with (map (fun _ : nat => Z_to_bv 8 0) (seq 0 (nbytes sz)))
by (rewrite map_const, length_seq; reflexivity).
replace (A + k) with (A + (0 + k)) by lia.
eapply (chunk_read segs E m A (mkChunk 0 (CZero len)) (0 + k)); [exact Hc | cbn; lia | cbn; unfold x_len in Hkn; rewrite Hcv in Hkn; cbn in Hkn; lia |].
intros i Hi. reflexivity.
+ destruct sz, sg; vm_compute; reflexivity.
-
destruct (0 <=? s0) eqn:Hs0; [|discriminate]. apply Z.leb_le in Hs0.
injection H as <-.
set (f := fun i : nat => match nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat with
| Some b0 => b0 | None => Z_to_bv 8 0 end).
assert (Hf : forall i, (i < nbytes sz)%nat -> nth_error (ed E d) (Z.to_nat (s0 + k) + i)%nat = Some (f i)).
{ intros i Hi. destruct (Hc (k + Z.of_nat i)) as (b0 & Hb1 & Hb2).
{ unfold c_len. cbn [c_val]. unfold x_len in Hkn. rewrite Hcv in Hkn. cbn [cv_len] in Hkn |- *. lia. }
cbn [cbyte c_val c_off] in Hb1.
replace (Z.to_nat (s0 + (k + Z.of_nat i))) with (Z.to_nat (s0 + k) + i)%nat in Hb1 by lia.
unfold f. rewrite Hb1. reflexivity. }
exists (map f (seq 0 (nbytes sz))). split.
+ replace (A + k) with (A + (0 + k)) by lia.
eapply (chunk_read segs E m A (mkChunk 0 (CData d s0 len)) (0 + k)); [exact Hc | cbn; lia | cbn; unfold x_len in Hkn; rewrite Hcv in Hkn; cbn in Hkn; lia |].
intros i Hi. cbn [cbyte c_val c_off]. rewrite <- Hf by exact Hi. f_equal. lia.
+ pose proof (loadres_sound E G sz sg (SData d (s0 + k) (N.of_nat (nbytes sz)))
(data_word E d (s0 + k) (N.of_nat (nbytes sz))) HG eq_refl) as HL.
rewrite HL, le_bytes_to_word_Z. f_equal. f_equal.
unfold data_word. rewrite Nat2N.id.
rewrite (firstn_skipn_map (nbytes sz) (Z.to_nat (s0 + k)) (ed E d) f Hf).
apply Z.mod_small.
pose proof (bytes_le_to_Z_nonneg (map f (seq 0 (nbytes sz)))).
pose proof (bytes_le_to_Z_bound (map f (seq 0 (nbytes sz)))) as Hb.
rewrite length_map, length_seq in Hb. lia.
Qed.
Lemma zone_find_idx_sound : forall G cs z a n idx k,
zone_find_idx G cs z a n = Some (idx, k) ->
In (mkAC BC_LTU idx (xz_count z)) cs /\ lin_diff a (zone_elem z idx) = Some k /\ 0 <= k /\ k + n <= xz_elt z.
Proof.
induction cs as [|[c ca cb] r IH]; cbn; intros z a n idx k H; [discriminate|].
assert (IH' : zone_find_idx G r z a n = Some (idx, k) ->
In (mkAC BC_LTU idx (xz_count z)) r /\ lin_diff a (zone_elem z idx) = Some k /\ 0 <= k /\ k + n <= xz_elt z)
by (intros; apply IH; assumption).
destruct c; try (destruct (IH' H) as (? & ? & ? & ?); auto; fail); try (destruct (IH' H); tauto).
destruct (sv_eqb cb (xz_count z)) eqn:Hcb; [|destruct (IH' H); tauto].
apply sv_eqb_eq in Hcb. subst cb.
destruct (lin_diff a (zone_elem z ca)) as [k0|] eqn:Hd; [|destruct (IH' H); tauto].
destruct ((0 <=? k0) && (k0 + n <=? xz_elt z)) eqn:Hk; [|destruct (IH' H); tauto].
injection H as <- <-. apply andb_prop in Hk as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
split; [left; reflexivity|]. auto.
Qed.
Lemma zone_find_sound : forall G zs a n z idx k,
zone_find G zs a n = Some (z, idx, k) ->
In z zs /\ In (mkAC BC_LTU idx (xz_count z)) (f_conds G)
/\ lin_diff a (zone_elem z idx) = Some k /\ 0 <= k /\ k + n <= xz_elt z.
Proof.
induction zs as [|z0 r IH]; cbn; intros a n z idx k H; [discriminate|].
destruct (zone_find_idx G (f_conds G) z0 a n) as [[i0 k0]|] eqn:Hf.
- injection H as <- <- <-. apply zone_find_idx_sound in Hf. tauto.
- destruct (IH a n z idx k H). tauto.
Qed.
Lemma conds_ok_In : forall E cs c, conds_ok E cs -> In c cs -> acond_ok E c.
Proof. intros E cs c H Hin. apply (proj1 (conds_ok_forall E cs) H). exact Hin. Qed.
Lemma zone_addr_exact : forall E G m rs z a n idx k,
facts_ok E G -> xzone_ok E m rs z ->
In (mkAC BC_LTU idx (xz_count z)) (f_conds G) ->
lin_diff a (zone_elem z idx) = Some k -> 0 <= k -> k + n <= xz_elt z -> 0 < n ->
bv_unsigned (sv_denot E a) = zone_lo E z + xz_elt z * bv_unsigned (sv_denot E idx) + k
/\ zone_lo E z <= bv_unsigned (sv_denot E a)
/\ bv_unsigned (sv_denot E a) + n <= zone_hi E z.
Proof.
intros E G m rs z a n idx k HG (Helt & Hhi & _ & _) Hc Hd Hk Hkn Hn.
pose proof (conds_ok_In E _ _ (proj1 (proj2 HG)) Hc) as Hlt.
unfold acond_ok in Hlt. cbn [ac_c ac_a ac_b branch_taken] in Hlt. unfold bv_ltu in Hlt. apply Z.ltb_lt in Hlt.
unfold zone_hi, zone_lo in *.
set (B := bv_unsigned (sv_denot E (xz_base z))) in *.
set (C := bv_unsigned (sv_denot E (xz_count z))) in *.
set (I := bv_unsigned (sv_denot E idx)) in *.
pose proof (u64_range (sv_denot E (xz_base z))) as HB. pose proof (u64_range (sv_denot E idx)) as HI.
assert (HIC : xz_elt z * I + xz_elt z <= xz_elt z * C) by nia.
assert (Hel : U E (zone_elem z idx) = B + xz_elt z * I).
{ unfold zone_elem. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
change (U E (xz_base z)) with B. change (U E idx) with I.
rewrite (zcanon_id (xz_elt z)) by lia.
rewrite (zcanon_id (I * xz_elt z)) by (unfold M64 in *; nia).
rewrite zcanon_id by (unfold M64 in *; nia). lia. }
assert (HUa : U E a = B + xz_elt z * I + k).
{ rewrite (lin_diff_exact E a _ k Hd); rewrite Hel; [lia|]. unfold M64 in *. nia. }
change (bv_unsigned (sv_denot E a)) with (U E a). rewrite HUa. nia.
Qed.
Lemma mem_ok_wbytes_outside : forall E m rs a bs,
mem_ok segs E m rs -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall b lo hi wlo whi x, In (b, lo, hi, wlo, whi) (skeleton rs) ->
a <= x < a + Z.of_nat (length bs) -> ~ (base_val E b + lo <= x < base_val E b + hi)) ->
mem_ok segs E (wbytes m (Z_to_bv 64 a) bs) rs.
Proof.
intros E m rs a bs (Hwf & Hok & Hpd) Ha Hnw Hsep.
split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hin. specialize (Hok r Hin).
destruct Hok as (Hb0 & Hb1 & Hw & Hcs).
pose proof (regions_wf_In _ _ Hwf Hin) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & _ & Hcin).
assert (Hsk : In (skel r) (skeleton rs)) by (apply in_map; exact Hin).
split; [exact Hb0|]. split; [exact Hb1|]. split.
- intros o Ho. eapply writable_at_grows; [apply wbytes_grows|]. apply Hw. exact Ho.
- rewrite Forall_forall in Hcs |- *. intros c Hc.
pose proof (proj1 (forallb_forall _ _) Hcin c Hc) as Hci. apply chunk_inside_facts in Hci.
destruct (Z.eq_dec (c_len c) 0) as [Hz|Hz].
{ intros i Hi. exfalso. lia. }
destruct bs as [|b0 bs'] eqn:Hbs.
{ cbn [wbytes]. apply Hcs. exact Hc. }
assert (Hlen : 0 < Z.of_nat (length bs)) by (subst bs; cbn; lia). rewrite <- Hbs in *. clear Hbs.
apply chunk_ok_wbytes_out; try lia.
+
destruct (Z_lt_le_dec (base_val E (r_base r) + c_off c + c_len c) (a + 1)) as [H1|H1]; [left; lia|].
destruct (Z_lt_le_dec (a + Z.of_nat (length bs)) (base_val E (r_base r) + c_off c + 1)) as [H2|H2]; [right; lia|].
exfalso. set (x := Z.max a (base_val E (r_base r) + c_off c)).
apply (Hsep (r_base r) (r_lo r) (r_hi r) (r_wlo r) (r_whi r) x); [exact Hsk| subst x; lia | subst x; lia].
+ apply Hcs. exact Hc.
Qed.
Lemma Forall_filter {A} : forall (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros P f l H. rewrite Forall_forall in *. intros x Hx. apply filter_In in Hx as [Hx _]. auto. Qed.
Lemma xzone_ok_mem : forall E m m' rs rs' z,
skeleton rs' = skeleton rs ->
(forall x, in_zone E z x -> m (Z_to_bv 64 x) <> None -> m' (Z_to_bv 64 x) <> None) ->
xzone_ok E m rs z -> xzone_ok E m' rs' z.
Proof.
intros E m m' rs rs' z Hsk Hm (H1 & H2 & H3 & H4).
split; [exact H1|]. split; [exact H2|]. split.
- intros x Hx. apply Hm; [exact Hx|]. apply H3. exact Hx.
- rewrite Hsk. exact H4.
Qed.
Lemma xchunk_ok_mem : forall E m m' zs c,
(forall x, in_zones E zs x -> 0 <= x < 2^64 -> mbyte segs m' x = mbyte segs m x) ->
xchunk_ok E m zs c -> xchunk_ok E m' zs c.
Proof.
intros E m m' zs c Hm (Hlen & Hnw & Hc & Hni & Hz).
split; [exact Hlen|]. split; [exact Hnw|]. split; [| split; [exact Hni| exact Hz]].
destruct Hz as (z & Hzin & Hzlo & Hzhi).
pose proof (u64_range (sv_denot E (x_addr c))) as HA.
intros i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
cbn [c_off] in *. unfold c_len in Hi. cbn [c_val] in Hi. unfold x_len in *.
rewrite Hm; [exact Hb2| | lia]. exists z. split; [exact Hzin|]. unfold in_zone. lia.
Qed.
Lemma in_wrange_extent : forall E rs x,
regions_wf rs = true -> in_wrange E rs x ->
exists b lo hi wlo whi, In (b, lo, hi, wlo, whi) (skeleton rs) /\ base_val E b + lo <= x < base_val E b + hi.
Proof.
intros E rs x Hwf (r & Hin & Hx).
pose proof (regions_wf_In _ _ Hwf Hin) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hw & _).
exists (r_base r), (r_lo r), (r_hi r), (r_wlo r), (r_whi r). split.
- change (In (skel r) (skeleton rs)). apply in_map. exact Hin.
- destruct Hw as [Hw|Hw]; lia.
Qed.
Lemma frame_zone_same : forall E rs zs m m' x,
regions_wf rs = true -> Forall (xzone_ok E m rs) zs -> frame_of E rs m m' ->
in_zones E zs x -> 0 <= x < 2^64 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
intros E rs zs m m' x Hwf Hzs Hfr (z & Hzin & Hx) Hxr. apply Hfr.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
intros Hw. apply in_wrange_extent in Hw as (b & lo & hi & wlo & whi & Hsk & Hin); [|exact Hwf].
rewrite Forall_forall in Hzs. destruct (Hzs z Hzin) as (_ & _ & _ & Hsep).
exact (Hsep b lo hi wlo whi x Hsk Hx Hin).
Qed.
Lemma frame_zone_mbyte : forall E rs zs m m' x,
regions_wf rs = true -> Forall (xzone_ok E m rs) zs -> frame_of E rs m m' ->
in_zones E zs x -> 0 <= x < 2^64 -> mbyte segs m' x = mbyte segs m x.
Proof.
intros E rs zs m m' x Hwf Hzs Hfr Hz Hxr. unfold mbyte.
rewrite (frame_zone_same E rs zs m m' x Hwf Hzs Hfr Hz Hxr). reflexivity.
Qed.
Lemma xmem_ok_frame : forall E m m' rs rs' cs cs' zs,
regions_wf rs = true -> skeleton rs' = skeleton rs -> frame_of E rs m m' ->
(forall P, Forall P cs -> Forall P cs') ->
xmem_ok E m rs cs zs -> xmem_ok E m' rs' cs' zs.
Proof.
intros E m m' rs rs' cs cs' zs Hwf Hsk Hfr Hsub [Hcs Hzs]. split.
- apply Hsub. rewrite Forall_forall in Hcs |- *. intros c Hc.
eapply xchunk_ok_mem; [|apply Hcs; exact Hc].
intros x Hx Hxr. eapply frame_zone_mbyte; eauto.
- rewrite Forall_forall in Hzs |- *. intros z Hz.
eapply xzone_ok_mem; [exact Hsk| | apply Hzs; exact Hz].
intros x Hx Hm. rewrite (frame_zone_same E rs zs m m' x Hwf); auto.
+ rewrite Forall_forall. exact Hzs.
+ exists z. auto.
+ destruct (Hzs z Hz) as (_ & Hhi & _). unfold in_zone, zone_hi, zone_lo in *.
pose proof (u64_range (sv_denot E (xz_base z))). lia.
Qed.
Section h.
Hypothesis Htbl : table_ok segs tbl.
Lemma Forall_id {A} : forall (P : A -> Prop) l, Forall P l -> Forall P l. Proof. auto. Qed.
Lemma two_idx_sound : forall E l i j m,
two_idx l = Some (i, j, m) -> 0 < m /\ lin_denot E l = m * (bv_unsigned (ew E j) - bv_unsigned (ew E i)).
Proof.
intros E l i j m H. unfold two_idx in H.
destruct l as [|[x cx] [|[y cy] [|]]]; try discriminate.
destruct ((0 <? cy) && (cx =? - cy)) eqn:H1.
- injection H as <- <- <-. apply andb_prop in H1 as [A B]. apply Z.ltb_lt in A. apply Z.eqb_eq in B.
cbn [lin_denot]. split; [lia|]. subst cx. lia.
- destruct ((0 <? cx) && (cy =? - cx)) eqn:H2; [|discriminate].
injection H as <- <- <-. apply andb_prop in H2 as [A B]. apply Z.ltb_lt in A. apply Z.eqb_eq in B.
cbn [lin_denot]. split; [lia|]. subst cy. lia.
Qed.
Lemma atom_lt_sound : forall E G i j,
facts_ok E G -> atom_lt G i j = true -> bv_unsigned (ew E i) < bv_unsigned (ew E j).
Proof.
intros E G i j HG H. unfold atom_lt in H.
assert (Hden : forall n, bv_unsigned (sv_denot E (SOff n 0)) = bv_unsigned (ew E n)).
{ intros n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
apply orb_prop in H as [H|H].
- destruct HG as (_ & Hc & _). pose proof (cond_assumed_sound E _ _ _ _ Hc H) as Hb.
cbn [branch_taken] in Hb. unfold bv_ltu in Hb. apply Z.ltb_lt in Hb. rewrite !Hden in Hb. exact Hb.
- destruct (itv_lt (sv_urange G (SOff i 0)) (sv_urange G (SOff j 0))) as [[|]|] eqn:Hl; try discriminate.
pose proof (proj1 (sv_ranges_sound E G (SOff i 0) HG)) as Hi.
pose proof (proj1 (sv_ranges_sound E G (SOff j 0) HG)) as Hj.
unfold sv_urange in Hl.
pose proof (itv_lt_sound _ _ _ _ true Hi Hj Hl) as Hb. apply Z.ltb_lt in Hb.
unfold U in Hb. rewrite !Hden in Hb. exact Hb.
Qed.
Lemma xsep_idx_sound : forall E G a n c,
facts_ok E G -> xsep_idx G a n c = true -> 0 <= n -> 0 <= x_len c ->
U E (x_addr c) + x_len c <= U E a \/ U E a + n <= U E (x_addr c).
Proof.
intros E G a n c HG H Hn Hl. unfold xsep_idx in H.
destruct (lin_nf a) as [[la ka]|] eqn:Hla; [|discriminate].
destruct (lin_nf (x_addr c)) as [[lc kc]|] eqn:Hlc; [|discriminate].
destruct (sv_urange G a) as [[al ah]|] eqn:Hra; [|discriminate].
destruct (sv_urange G (x_addr c)) as [[cl ch]|] eqn:Hrc; [|discriminate].
destruct (two_idx (lin_clean (lin_merge lc (lin_scale (-1) la)))) as [[[i j] m]|] eqn:Ht; [|discriminate].
destruct (sv_urange G (SOff i 0)) as [[il ih]|] eqn:Hri; [|discriminate].
destruct (sv_urange G (SOff j 0)) as [[jl jh]|] eqn:Hrj; [|discriminate].
pose proof (two_idx_sound E _ i j m Ht) as [Hm Hdl].
rewrite lin_clean_denot, lin_merge_denot, lin_scale_denot in Hdl.
pose proof (lin_nf_sound E a la ka Hla) as Ua. pose proof (lin_nf_sound E (x_addr c) lc kc Hlc) as Uc.
pose proof (sv_urange_sound E G a al ah HG Hra) as Ra.
pose proof (sv_urange_sound E G (x_addr c) cl ch HG Hrc) as Rc.
pose proof (sv_urange_sound E G (SOff i 0) il ih HG Hri) as Ri.
pose proof (sv_urange_sound E G (SOff j 0) jl jh HG Hrj) as Rj.
cbn [sv_denot] in Ri, Rj. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Ri, Rj.
change (bv_unsigned (sv_denot E a)) with (U E a) in Ra.
change (bv_unsigned (sv_denot E (x_addr c))) with (U E (x_addr c)) in Rc.
pose proof (U_range E a) as HUa. pose proof (U_range E (x_addr c)) as HUc.
pose proof (u64_range (ew E i)) as Hi64. pose proof (u64_range (ew E j)) as Hj64.
set (Ui := bv_unsigned (ew E i)) in *. set (Uj := bv_unsigned (ew E j)) in *.
set (A := lin_denot E lc + kc) in *. set (B := lin_denot E la + ka) in *.
set (P := m * (Uj - Ui)) in *.
assert (HAB : A - B = P + (kc - ka)) by (subst A B P; lia).
assert (Hmod : (U E (x_addr c) - (U E a + P + (kc - ka))) mod M64 = 0).
{ rewrite Uc, Ua. unfold M64 in *.
replace (A mod 2 ^ 64 - (B mod 2 ^ 64 + P + (kc - ka)))
with ((A mod 2 ^ 64 - A) - (B mod 2 ^ 64 - B)) by lia.
rewrite (Z.mod_eq A (2^64)) by lia. rewrite (Z.mod_eq B (2^64)) by lia.
replace (A - 2 ^ 64 * (A / 2 ^ 64) - A - (B - 2 ^ 64 * (B / 2 ^ 64) - B)) with ((B / 2^64 - A / 2^64) * 2^64) by lia.
apply Z_mod_mult. }
apply Z.mod_divide in Hmod as [q Hq]; [| unfold M64; lia].
unfold M64 in *.
apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H3]; apply andb_prop in H1 as [H1 H2].
- apply atom_lt_sound with (E := E) in H1; [|exact HG]. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
fold Ui in H1. fold Uj in H1.
assert (HP1 : P <= m * jh) by (subst P; apply Z.mul_le_mono_nonneg_l; lia).
assert (HP2 : m * 1 <= P) by (subst P; apply Z.mul_le_mono_nonneg_l; lia).
rewrite Z.mul_1_r in HP2. clearbody P.
assert (q = 0) by lia. subst q. right. lia.
- apply atom_lt_sound with (E := E) in H1; [|exact HG]. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
fold Ui in H1. fold Uj in H1.
assert (HP1 : m * (Ui - Uj) <= m * ih) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (HP2 : m * 1 <= m * (Ui - Uj)) by (apply Z.mul_le_mono_nonneg_l; lia).
rewrite Z.mul_1_r in HP2.
assert (HP : P = - (m * (Ui - Uj))) by (subst P; lia).
set (Q := m * (Ui - Uj)) in *. clearbody Q. clearbody P. subst P.
assert (q = 0) by lia. subst q. left. lia.
Qed.
Lemma xsep_itv_sound : forall E G a n c,
facts_ok E G -> xsep_itv G a n c = true -> 0 <= n -> 0 <= x_len c ->
U E (x_addr c) + x_len c <= U E a \/ U E a + n <= U E (x_addr c).
Proof.
intros E G a n c HG H Hn Hl. unfold xsep_itv in H.
destruct (sv_urange G a) as [[al ah]|] eqn:Ha; [|discriminate].
destruct (sv_urange G (x_addr c)) as [[cl ch]|] eqn:Hc; [|discriminate].
pose proof (sv_urange_sound E G a al ah HG Ha) as Ra. pose proof (sv_urange_sound E G (x_addr c) cl ch HG Hc) as Rc.
change (bv_unsigned (sv_denot E a)) with (U E a) in Ra. change (bv_unsigned (sv_denot E (x_addr c))) with (U E (x_addr c)) in Rc.
pose proof (U_range E a) as HUa. pose proof (U_range E (x_addr c)) as HUc.
apply orb_prop in H as [H|H].
{ apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia. }
destruct (lin_diff (x_addr c) a) as [d|] eqn:Hd; [|discriminate].
pose proof (lin_diff_sound E _ _ d Hd) as HU. unfold M64 in *.
apply orb_prop in H as [H|H]; apply andb_prop in H as [Q1 Q2].
- apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. right. rewrite HU. rewrite Z.mod_small by lia. lia.
- apply Z.leb_le in Q1. apply Z.leb_le in Q2. left. rewrite HU. rewrite Z.mod_small by lia. lia.
Qed.
Lemma xsep_sound : forall E G a n c,
facts_ok E G -> xsep G a n c = true -> 0 <= n -> 0 <= x_len c ->
U E (x_addr c) + x_len c <= U E a \/ U E a + n <= U E (x_addr c).
Proof.
intros E G a n c HG H Hn Hl. unfold xsep in H. apply orb_prop in H as [H|H];
[eapply xsep_itv_sound; eauto | eapply xsep_idx_sound; eauto].
Qed.
Lemma xpass_sound : forall E xs ss' cs' ms,
xst_ok E xs ms -> sym_step segs tbl (xs_ss xs) = SRun ss' ->
(forall P, Forall P (xs_chunks xs) -> Forall P cs') ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms'
/\ xst_ok E (mkXS ss' cs' (xs_zones xs) (xs_dirty xs)) ms'
/\ skeleton (ss_mem ss') = skeleton (ss_mem (xs_ss xs))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs) (ms_mem ms) (ms_mem ms').
Proof.
intros E xs ss' cs' ms [HS HX] Hst Hsub.
destruct (sym_step_sound segs tbl Htbl E (xs_ss xs) ss' ms HS Hst) as (ms' & Hstep & HS' & Hfr).
pose proof (sym_step_skeleton segs tbl (xs_ss xs) ss' Hst) as Hsk.
exists ms'. split; [exact Hstep|]. split; [|split; [exact Hsk| apply frame_xframe; exact Hfr]].
split; [exact HS'|]. cbn [xs_ss xs_chunks xs_zones].
eapply xmem_ok_frame; [apply (st_ok_regions_wf segs E _ ms HS) | exact Hsk | exact Hfr | exact Hsub | exact HX].
Qed.
Theorem xsym_step_sound : forall E xs xs' ms,
xst_ok E xs ms -> xsym_step xs = XRun xs' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms'
/\ xst_ok E xs' ms'
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ (forall e, In e (xs_dirty xs) -> In e (xs_dirty xs'))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
intros E xs xs' ms HX H.
destruct xs as [ss cs zs dd]. cbn [xs_ss xs_chunks xs_zones xs_dirty] in *.
unfold xsym_step in H. cbn [xs_ss xs_chunks xs_zones xs_dirty] in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec.
{ destruct (sym_step segs tbl ss); discriminate. }
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
Ltac pass E ss cs zs dd ms HX Hst H sub :=
injection H as <-; unfold xwith; cbn [xs_ss xs_chunks xs_zones xs_dirty];
let ms' := fresh "ms'" in
destruct (xpass_sound E (mkXS ss cs zs dd) _ _ ms HX Hst sub) as (ms' & ?A & ?B & ?C & ?D);
cbn [xs_ss xs_chunks xs_zones xs_dirty] in *;
exists ms'; split; [exact A| split; [exact B| split; [exact C| split; [reflexivity| split; [auto| exact D]]]]].
destruct i;
try (destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate;
pass E ss cs zs dd ms HX Hst H (fun P (HP : Forall P cs) => HP)).
-
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate.
{ pass E ss cs zs dd ms HX Hst H (fun P (HP : Forall P cs) => HP). }
destruct (xload (ss_facts ss) cs (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) sz signed)
as [v|] eqn:Hxl; [|discriminate].
injection H as <-. unfold xwith. cbn [xs_ss xs_chunks xs_zones xs_dirty].
destruct HX as [HS [Hcs Hzs]]. cbn [xs_ss xs_chunks xs_zones] in Hcs, Hzs.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst fregs pcv pend fcsr rom.
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf.
destruct (xload_sound E (ss_facts ss) mem zs cs _ sz signed v HG Hcs Hxl) as (bs & Hrd & Hv).
rewrite s_alu2_sound in Hrd by exact HG. cbn [sv_denot alu64 alu] in Hrd.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). rewrite Hec, Hd.
assert (HR : forall r, rget (Core regs fp_regs (Z_to_bv 64 (ss_pc ss)) fp_csr resv) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR.
rewrite sext64_lit in *.
destruct sz; cbn [nbytes nbits] in Hrd, Hv;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
eexists; (split; [reflexivity|]);
(split; [split; [apply st_ok_machL; cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4] | cbn [ms_mem]; split; assumption]
| split; [reflexivity| split; [reflexivity| split; [auto| cbn [ms_mem]; apply xframe_refl]]]]);
rewrite Hv, ?bv_extract_0_64; cbn [load_result nbits]; destruct signed; reflexivity.
-
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate.
{ pass E ss cs zs dd ms HX Hst H (fun P (HP : Forall P cs) =>
Forall_filter P (xsep (ss_facts ss) (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) (Z.of_nat (nbytes sz))) cs HP). }
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|].
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (zone_find (ss_facts ss) zs a (Z.of_nat (nbytes sz))) as [[[z idx] k]|] eqn:Hzf; [|discriminate].
injection H as <-. cbn [xs_ss xs_chunks xs_zones xs_dirty].
destruct HX as [HS [Hcs Hzs]]. cbn [xs_ss xs_chunks xs_zones] in Hcs, Hzs.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst fregs pcv pend fcsr rom. rewrite Hrv in Hresv. cbn [resv_denot] in Hresv. subst resv.
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf.
apply zone_find_sound in Hzf as (Hzin & Hcin & Hld & Hk0 & Hkn).
pose proof (proj1 (Forall_forall _ _) Hzs z Hzin) as Hz.
pose proof (nbytes_pos sz) as Hnb.
destruct (zone_addr_exact E (ss_facts ss) mem (ss_mem ss) z a (Z.of_nat (nbytes sz)) idx k HG Hz Hcin Hld Hk0 Hkn ltac:(lia))
as (HA & HAlo & HAhi).
destruct Hz as (Helt & Hzhi & Halloc & Hsep).
set (A := bv_unsigned (sv_denot E a)) in *.
pose proof (u64_range (sv_denot E a)) as HAr. fold A in HAr.
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 A).
{ subst A. rewrite lit_of_word. subst a. rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
assert (Hok : store_ok segs mem (Z_to_bv 64 A) (nbytes sz) = true).
{ apply store_ok_of_all.
- rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). lia.
- intros x Hx. rewrite Z_to_bv_unsigned, bv_wrap_small in Hx by (change (bv_modulus 64) with (2^64); lia).
rewrite <- (lit_of_word x). unfold wview.
destruct (mem (Z_to_bv 64 (bv_unsigned x))) eqn:Hmx; [discriminate|].
exfalso. apply (Halloc (bv_unsigned x)); [unfold in_zone; lia| exact Hmx]. }
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). rewrite Hec, Hd.
assert (HR : forall r, rget (Core regs fp_regs (Z_to_bv 64 (ss_pc ss)) fp_csr None) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR.
rewrite ?Haddr.
assert (Hpost : forall n, n = nbytes sz ->
let m' := wbytes mem (Z_to_bv 64 A) (st_bytes n (sv_denot E (sr_get (ss_regs ss) rs2))) in
mem_ok segs E m' (ss_mem ss)
/\ xmem_ok E m' (ss_mem ss)
(mkX a (CVal (N.of_nat n) (sr_get (ss_regs ss) rs2)) :: xfilter (ss_facts ss) a (Z.of_nat n) cs) zs
/\ xframe E (ss_mem ss) ((a, Z.of_nat n) :: dd) mem m').
{ intros n ->. cbn zeta.
assert (Hlen : length (st_bytes (nbytes sz) (sv_denot E (sr_get (ss_regs ss) rs2))) = nbytes sz)
by (unfold st_bytes; apply length_zbytes).
split; [|split].
- apply mem_ok_wbytes_outside; [exact Hmem| lia | rewrite Hlen; lia |].
intros b lo hi wlo whi x Hsk Hx. rewrite Hlen in Hx. apply (Hsep b lo hi wlo whi x Hsk). unfold in_zone. lia.
- split.
+ constructor.
*
split; [unfold x_len; cbn [x_val cv_len]; lia|].
split; [unfold x_len; cbn [x_val cv_len x_addr]; fold A; rewrite nat_N_Z; lia|].
split.
{ unfold x_addr, x_val. fold A.
replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
apply new_chunk_ok; [lia| rewrite Hlen; lia | cbn [cv_len]; rewrite Hlen; lia |].
intros i Hi. rewrite Hlen in Hi. apply st_bytes_cbyte. exact Hi. }
split; [exact I|]. exists z. split; [exact Hzin|]. unfold x_addr, x_len, x_val. cbn [cv_len]. fold A. lia.
*
unfold xfilter. rewrite Forall_forall in Hcs |- *. intros c Hc.
apply filter_In in Hc as [Hc Hsepc]. specialize (Hcs c Hc).
destruct Hcs as (Hl0 & Hnw & Hck & Hni & Hzc).
split; [exact Hl0|]. split; [exact Hnw|]. split; [| split; [exact Hni| exact Hzc]].
destruct (Z.eq_dec (x_len c) 0) as [Hz0|Hz0]; [intros i Hi; exfalso; unfold c_len in Hi; cbn in Hi; unfold x_len in Hz0; lia|].
apply xsep_sound with (E := E) in Hsepc; [| exact HG | lia | lia].
change (U E a) with A in Hsepc. unfold U in Hsepc.
replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (f_equal; lia).
pose proof (u64_range (sv_denot E (x_addr c))).
apply (chunk_ok_wbytes_out segs E mem (bv_unsigned (sv_denot E (x_addr c))) (mkChunk 0 (x_val c)) (A + 0));
unfold c_len; cbn [c_off c_val]; try (rewrite ?Hlen; unfold x_len in *; lia).
exact Hck.
+ rewrite Forall_forall in Hzs |- *. intros z' Hz'. eapply xzone_ok_mem; [reflexivity| | apply Hzs; exact Hz'].
intros x _ Hm. apply (wbytes_grows _ mem). exact Hm.
- intros x Hw Hzx.
destruct (Z_lt_le_dec (bv_unsigned x) A).
+ apply wbytes_below; rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia); [rewrite Hlen; lia| lia].
+ destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (nbytes sz))).
* exfalso. apply Hzx. exists a, (Z.of_nat (nbytes sz)). split; [left; reflexivity|]. fold A. lia.
* apply wbytes_above. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). rewrite Hlen. lia. }
destruct sz; cbn [nbytes nbits] in Hok, Hpost |- *;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ?Haddr; rewrite Hok; unfold inval_resv;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_8, ?st_bytes_16, ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
(destruct (Hpost _ eq_refl) as (HM' & HX' & HF'));
eexists; (split; [reflexivity|]);
(split; [split; [apply st_ok_machL; cbn; auto; apply pc_plus4 | cbn [ms_mem]; exact HX']
| split; [reflexivity| split; [reflexivity| split; [intros e He; right; exact He| cbn [ms_mem]; exact HF']]]]).
-
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate.
pass E ss cs zs dd ms HX Hst H (fun P (HP : Forall P cs) => Forall_filter P (xsep (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) cs HP).
Qed.
Theorem xsym_step_ecall : forall E xs xs' ms,
xst_ok E xs ms -> xsym_step xs = XEcall xs' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ xst_ok_ecall E xs' ms'
/\ ms_mem ms' = ms_mem ms /\ xs_ss xs' = xs_ss xs /\ xs_chunks xs' = xs_chunks xs /\ xs_zones xs' = xs_zones xs
/\ xs_dirty xs' = xs_dirty xs.
Proof.
intros E xs xs' ms [HS HX] H.
destruct xs as [ss cs zs dd]. cbn [xs_ss xs_chunks xs_zones xs_dirty] in *.
unfold xsym_step in H. cbn [xs_ss xs_chunks xs_zones xs_dirty] in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec.
- destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate. injection H as <-.
destruct (sym_step_ecall segs tbl Htbl E ss ss1 ms HS Hst) as (ms' & Hstep & HS' & Hm & Hss). subst ss1.
exists ms'. unfold xwith. cbn [xs_ss xs_chunks xs_zones xs_dirty].
split; [exact Hstep|]. split; [| rewrite Hm; auto]. split; [exact HS'|]. cbn. rewrite Hm. exact HX.
- destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4); cbn [negb] in H; [|discriminate].
assert (Hno : forall ss1, sym_step segs tbl ss = SEcall ss1 -> False).
{ intros ss1 Hst. unfold sym_step in Hst. rewrite Hlk in Hst. cbv zeta in Hst. rewrite Hec in Hst.
rewrite Hd in Hst.
destruct (negb (isz =? 4)); [discriminate|].
destruct i; try discriminate;
repeat match type of Hst with
| context [match ?x with _ => _ end] => destruct x; try discriminate
end. }
destruct i;
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hst; try discriminate;
try (exfalso; exact (Hno ss1 eq_refl));
repeat match type of H with
| context [match ?x with _ => _ end] => destruct x; try discriminate
end.
Qed.
Theorem xsym_run_sound' : forall fuel E xs xs' st ms,
xst_ok E xs ms -> xsym_run fuel xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ (forall e, In e (xs_dirty xs) -> In e (xs_dirty xs'))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros E xs xs' st ms HX H; cbn [xsym_run] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
- destruct (xsym_step xs) as [xs1|xs1|why] eqn:Hs.
+ destruct (xsym_step_sound E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hsk1 & Hz1 & Hd1 & Hfr1).
destruct (IH E xs1 xs' st ms1 HX1 H) as (ms' & Hms & HX' & Hsk & Hz & Hd & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX'|]. split; [congruence|]. split; [congruence|]. split; [auto|].
eapply xframe_trans; [symmetry; exact Hsk1 | eapply xframe_mono; [exact Hd| exact Hfr1] | exact Hfr].
+ injection H as <- <-.
destruct (xsym_step_ecall E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hm & Hss & Hcs & Hzs & Hdd).
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX1|]. rewrite Hss, Hzs, Hm, Hdd. split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
Qed.
Lemma xst_ok_clear_dirty : forall E xs ms, xst_ok E xs ms -> xst_ok E (clear_dirty xs) ms.
Proof. intros E xs ms [HS HX]. split; assumption. Qed.
Theorem xsym_run_sound : forall n E xs xs' st ms,
xst_ok E xs ms -> xsym_runN n xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
intros n E xs xs' st ms HX H. unfold xsym_runN in H.
destruct (xsym_run_sound' _ E (clear_dirty xs) xs' st ms (xst_ok_clear_dirty E xs ms HX) H)
as (ms' & A & B & C & D & _ & F).
exists ms'. auto 10.
Qed.
Theorem xsym_run_to_sound' : forall fuel stop E xs xs' st ms,
xst_ok E xs ms -> xsym_run_to fuel stop xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ (forall e, In e (xs_dirty xs) -> In e (xs_dirty xs'))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stop E xs xs' st ms HX H; cbn [xsym_run_to] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
- destruct (ss_pc (xs_ss xs) =? stop).
{ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]]. }
destruct (xsym_step xs) as [xs1|xs1|why] eqn:Hs.
+ destruct (xsym_step_sound E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hsk1 & Hz1 & Hd1 & Hfr1).
destruct (IH stop E xs1 xs' st ms1 HX1 H) as (ms' & Hms & HX' & Hsk & Hz & Hd & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX'|]. split; [congruence|]. split; [congruence|]. split; [auto|].
eapply xframe_trans; [symmetry; exact Hsk1 | eapply xframe_mono; [exact Hd| exact Hfr1] | exact Hfr].
+ injection H as <- <-.
destruct (xsym_step_ecall E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hm & Hss & Hcs & Hzs & Hdd).
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX1|]. rewrite Hss, Hzs, Hm, Hdd. split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
Qed.
Theorem xsym_run_to_sound : forall n stop E xs xs' st ms,
xst_ok E xs ms -> xsym_run_toN n stop xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E xs xs' st ms HX H. unfold xsym_run_toN in H.
destruct (xsym_run_to_sound' _ stop E (clear_dirty xs) xs' st ms (xst_ok_clear_dirty E xs ms HX) H)
as (ms' & A & B & C & D & _ & F).
exists ms'. auto 10.
Qed.
Theorem xsym_run_tos_sound' : forall fuel stops E xs xs' st ms,
xst_ok E xs ms -> xsym_run_tos fuel stops xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ (forall e, In e (xs_dirty xs) -> In e (xs_dirty xs'))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stops E xs xs' st ms HX H; cbn [xsym_run_tos] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
- destruct (xsym_step xs) as [xs1|xs1|why] eqn:Hs.
+ destruct (xsym_step_sound E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hsk1 & Hz1 & Hd1 & Hfr1).
assert (Hgo : forall xs2 st2, xsym_run_tos fuel stops xs1 = (xs2, st2) \/ (xs2 = xs1 /\ st2 = XS_running) ->
exists ms', msteps segs ms ms' /\
match st2 with XS_ecall => xst_ok_ecall E xs2 ms' | _ => xst_ok E xs2 ms' end
/\ skeleton (ss_mem (xs_ss xs2)) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs2 = xs_zones xs
/\ (forall e, In e (xs_dirty xs) -> In e (xs_dirty xs2))
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs2) (ms_mem ms) (ms_mem ms')).
{ intros xs2 st2 [Hrun | [-> ->]].
- destruct (IH stops E xs1 xs2 st2 ms1 HX1 Hrun) as (ms' & Hms & HX' & Hsk & Hz & Hd & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX'|]. split; [congruence|]. split; [congruence|]. split; [auto|].
eapply xframe_trans; [symmetry; exact Hsk1 | eapply xframe_mono; [exact Hd| exact Hfr1] | exact Hfr].
- exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX1|]. split; [exact Hsk1|]. split; [exact Hz1|]. split; [exact Hd1| exact Hfr1]. }
destruct (existsb (Z.eqb (ss_pc (xs_ss xs1))) stops).
* injection H as <- <-. apply (Hgo xs1 XS_running). right. auto.
* apply (Hgo xs' st). left. exact H.
+ injection H as <- <-.
destruct (xsym_step_ecall E xs xs1 ms HX Hs) as (ms1 & Hstep & HX1 & Hm & Hss & Hcs & Hzs & Hdd).
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HX as [(_ & _ & Hp & _) _]. exact Hp. }
split; [exact HX1|]. rewrite Hss, Hzs, Hm, Hdd. split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HX|].
split; [reflexivity|]. split; [reflexivity| split; [auto| apply xframe_refl]].
Qed.
Theorem xsym_run_tos_sound : forall n stops E xs xs' st ms,
xst_ok E xs ms -> xsym_run_tosN n stops xs = (xs', st) ->
exists ms', msteps segs ms ms' /\
match st with
| XS_ecall => xst_ok_ecall E xs' ms'
| _ => xst_ok E xs' ms'
end
/\ skeleton (ss_mem (xs_ss xs')) = skeleton (ss_mem (xs_ss xs))
/\ xs_zones xs' = xs_zones xs
/\ xframe E (ss_mem (xs_ss xs)) (xs_dirty xs') (ms_mem ms) (ms_mem ms').
Proof.
intros n stops E xs xs' st ms HX H. unfold xsym_run_tosN in H.
destruct (xsym_run_tos_sound' _ stops E (clear_dirty xs) xs' st ms (xst_ok_clear_dirty E xs ms HX) H)
as (ms' & A & B & C & D & _ & F).
exists ms'. auto 10.
Qed.
End h.
End g.
