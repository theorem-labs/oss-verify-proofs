(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0e.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0c.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Hypothesis AMH : alloc_meta_hyp B.
Ltac bvlit := split; apply Z.leb_le; vm_compute; reflexivity.
Ltac creg := unfold callee_saved;
match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.
Ltac st_region HS i name :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
pose proof (st_ok_region segs E ss ms i rr HS ltac:(vm_compute; reflexivity)) as name end end.
Ltac st_chunk HS i c name :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
pose proof (st_ok_chunk segs E ss ms i rr c HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as name;
cbn [base_val r_base] in name end end.
Ltac st_writable HS i o :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with Some ?rr =>
apply (st_ok_writable segs E ss ms i rr o HS ltac:(vm_compute; reflexivity)) end end.
Lemma fold_off_0 : forall x, 0 <= x < 256 -> fold_off 0 x = 0.
Proof. intros x Hx. pose proof (fold_off_ok 0 x ltac:(lia) Hx). lia. Qed.
Lemma enframe_bridge : forall n A3 (ctr64 aZ : Z),
let mp := YN2f.maplen n in let b0 := Z_to_bv 8 0 in
32 <= mp -> e_stride n = dlen n - UNIT -> 0 <= e_slack n -> 0 <= e_off0 n A3 < 256 ->
0 <= ctr64 -> Z.land ctr64 255 = Z.land (ctr5 A3) 255 ->
stride 0 mp 0 = e_stride n /\
off n ctr64 0 mp 0 b0 b0 b0 = e_off n A3 /\
start aZ 0 0 mp 0 = aZ + 16 /\
q aZ 0 n ctr64 0 mp 0 b0 b0 b0 = aZ + UNIT + UNIT * e_off n A3 /\
end_ aZ 0 0 mp 0 = aZ + dlen n - 4 /\
reserved n ctr64 0 mp 0 b0 b0 b0 = e_reserved n A3 /\
code n ctr64 0 mp 0 b0 b0 b0 = e_rsv n A3 /\
hdr16v 0 n ctr64 0 mp 0 b0 b0 b0 = e_off n A3.
Proof.
intros n A3 ctr64 aZ mp b0 Hmp Hst Hsl Ho0 Hc Hland.
assert (ST : stride 0 mp 0 = e_stride n).
{ unfold stride, mapped1. rewrite (proj2 (Z.eqb_neq mp 0)) by lia. cbn [negb andb Z.eqb]. unfold e_stride. fold mp. unfold UNIT. lia. }
assert (OFF : off n ctr64 0 mp 0 b0 b0 b0 = e_off n A3).
{ unfold off, slack, YN04.off0, off0src, h3. rewrite ST. subst b0. change (bv_unsigned (Z_to_bv 8 0) =? 0) with true. cbn [negb andb].
unfold e_off, e_off0. change ((e_stride n - 4 - n) / 16) with (e_slack n).
destruct (Z.eqb_spec (e_slack n) 0) as [E|E].
- rewrite E. rewrite !fold_off_0; [reflexivity | lia |]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound ctr64 (2 ^ 8)). lia.
- rewrite Hland. reflexivity. }
assert (STA : start aZ 0 0 mp 0 = aZ + 16) by (unfold start; rewrite ST; lia).
split; [exact ST|]. split; [exact OFF|]. split; [exact STA|].
split; [unfold q; rewrite STA, OFF; unfold UNIT; lia|].
split; [unfold end_; rewrite STA, ST, Hst; unfold UNIT; lia|].
assert (RS : reserved n ctr64 0 mp 0 b0 b0 b0 = e_reserved n A3) by (unfold reserved, e_reserved; rewrite ST, OFF; unfold IB, UNIT; lia).
split; [exact RS|]. split; [unfold code, e_rsv; rewrite RS; reflexivity|].
unfold hdr16v. rewrite OFF, ST, Z.mul_0_r. reflexivity.
Qed.
Lemma sk_ret1 : map (fun r => (r_base r, r_wlo r, r_whi r)) (ss_mem ss_ret1) =
[(Some 34%nat, 0, 8); (Some 35%nat, 16, 40); (Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, CTX + 12, CTX + 16); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Definition wr1 (regs : bvmap 5 word) (a g : word) (x : Z) : Prop :=
scratch B regs x \/ (bv_unsigned a <= x < bv_unsigned a + 8) \/ (bv_unsigned g + 16 <= x < bv_unsigned g + 40) \/ (CTX + 12 <= x < CTX + 16).
Lemma in_wrange_ret1 : forall regs seq ctr useq a g xr rs x,
map (fun r => (r_base r, r_wlo r, r_whi r)) rs =
[(Some 34%nat, 0, 8); (Some 35%nat, 16, 40); (Some 2%nat, -8192, 0); (None, 0, 0); (None, 0, 0); (None, CTX + 12, CTX + 16); (None, ERRNO, ERRNO + 4)] ->
in_wrange (E_mi regs seq ctr useq a g xr) rs x -> wr1 regs a g x.
Proof.
intros regs seq ctr useq a g xr rs x Hsk Hw. apply in_wrange_list in Hw as (t & Hin & Hx). rewrite Hsk in Hin.
unfold wr1, scratch, spZ, ALLOC_STACK. rewrite B_errno. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd base_val ew E_mi] in Hx; lia.
Qed.
Lemma some_tail : forall L A regs mem md n (a : word) L3 A3 regs6 mem6 md3 m,
call_pre B (MRx B) L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2 ^ 62 ->
let sp := bv_unsigned (getr regs 2) in
let g := loc_addr L3 (LMem m) in
grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
midrep B L3 A3 mem6 md3 -> layout_le (dA2 A n) (L1 L A a) L3 -> am_frame (dA2 A n) A3 -> ub_same (dA2 A n) A3 ->
Inv [m] None U0 A3 -> (forall g' am, usedX [m] A3 g' am <-> usedX [] A g' am) -> In m (keys A3) ->
(MT A3 m = Some MRaw \/ MT A3 m = Some (MFree None None)) ->
bounded A3 -> ama_ok A3 -> (exists vm3, md3 = with_vmmaps vm3 (md1 md a (dlen n))) ->
getr regs6 10 = Z_to_bv 64 g -> getr regs6 2 = Z_to_bv 64 (sp - 48) -> getr regs6 3 = getr regs 3 -> getr regs6 4 = Z_to_bv 64 TP ->
getr regs6 8 = getr regs 10 -> getr regs6 9 = Z_to_bv 64 LOCK -> getr regs6 18 = Z_to_bv 64 (2 ^ 64 - 1) ->
getr regs6 19 = Z_to_bv 64 (n + 20) -> getr regs6 20 = a -> (forall r, 21 <= bv_unsigned r <= 27 -> getr regs6 r = getr regs r) ->
(forall k off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
(k < 8)%nat -> mbyte src0segs mem6 (sp + off + Z.of_nat k) = Some (byte_of_word (getr regs r) (Z.of_nat k))) ->
(forall x, sp - 8192 <= x < sp -> writable_at src0segs mem6 x) ->
(forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem6 x) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> ~ in_nonmap_region L3 A3 x ->
~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> mem6 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
(forall i, 0 <= i < dlen n -> mbyte src0segs mem6 (bv_unsigned a + i) = Some (Z_to_bv 8 0)) ->
(forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present mem6 x) ->
mreal src0segs (mkCfg (mkst regs6 (Z_to_bv 64 RA_AM) mem6 (seg_rom src0segs)) md3)
(ibind (enframe m 0 n (dm_ctr A3) FUser (dm_A5 n A m A3)) (fun '(p, s6) => IRet (Some p, s6)))
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
intros L A regs mem md n a L3 A3 regs6 mem6 md3 m PRE Hn Hrange sp g GR MID3 LE3 FR3 UB3 HI3 EU3 Km Mm HB3 HA3 VM3
R10 R2 R3 R4 R8 R9 R18 R19 R20 R2x STK Kws Kwe FR6 Z6 P6.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Hauxv).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
pose proof (dlen_facts n (proj1 Hrange)) as (D1 & D2 & D3 & D4 & D5).
pose proof (grant_facts B L A mem md a (dlen n) MX (conj D1 D2) GR) as (Gal & Gpos & Gceil & _ & _).
pose proof (inv_ctx HW) as (Lact & Lus & Luseq & Lbo & Uus & Uuseq & Ubo & Rseq & Rctr & _).
assert (HT : MMAP_THRESHOLD = 131052) by reflexivity. assert (PG : PGSZ = 4096) by reflexivity. rewrite PG in Gal.
assert (Hn' : bv_unsigned (getr regs 10) = n) by (rewrite Hn; apply u64_of_Z; lia).
unfold spZ in *. fold sp in Hal, Hceil, Hsp63, Hstk. unfold ALLOC_STACK in Hceil, Hstk.
destruct (mid_md _ _ _ _ _ MID3) as (Hh3 & Hlz3 & Hmat3).
assert (NI : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> ~ in_img B x).
{ intros x Hx Hi. exact (new_disjoint_img B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR x Hi Hx). }
assert (Haimg : bv_unsigned a + 131072 <= 0x1f000 \/ 0x51000 <= bv_unsigned a).
{ destruct (Z_lt_le_dec (bv_unsigned a) 0x51000); [left|right; lia].
destruct (Z_lt_le_dec 0x1f000 (bv_unsigned a + 131072)); [|lia]. exfalso.
apply (NI (Z.max (bv_unsigned a) 0x1f000)); [lia|]. apply src0_rwseg_img. lia. }
destruct (D3_pre B L A mem md a n L3 A3 mem6 md3 m) as (MH & [OC1 OC2] & MPRES & CTR6 & OLDB & GB & L3r0 & L3old & UB3A & P6A); try assumption.
1-4: first [exact src0_ENC | exact src0_ENS | exact src0_ERRIMG | exact src0_SNC].
fold g in MH, OC1, OC2, MPRES, OLDB, GB.
destruct MH as (rr & rgm & Hrr & Hlrr & Hkrr & Hner & Gm1 & Gm2 & Galign & Glo & Ghi & Gimg).
assert (Ug : bv_unsigned (Z_to_bv 64 g) = g) by (apply u64_of_Z; lia).
assert (Himg_g : g + 40 <= 0x1f000 \/ 0x51000 <= g).
{ destruct (Z_lt_le_dec g 0x51000); [left|right; lia]. destruct (Z_lt_le_dec 0x1f000 (g + 40)); [|lia]. exfalso.
apply (Gimg g); [lia|]. apply in_img1_img. unfold in_img1. lia. }
assert (DISJ : g + 40 <= bv_unsigned a \/ bv_unsigned a + dlen n <= g).
{ destruct (Z_lt_le_dec (bv_unsigned a) (g + 40)); [|left; lia]. destruct (Z_lt_le_dec g (bv_unsigned a + dlen n)); [|right; lia]. exfalso.
apply (proj1 (GB (Z.max (bv_unsigned a) g) ltac:(lia))). lia. }
change (dm_ctr A3) with (ctr5 A3). change (dm_A5 n A m A3) with (A5 A n A3 m).
rewrite (enframe_direct_eval A n A3 HW (proj1 Hrange) FR3 m HI3 EU3 (proj2 Hrange)).
match goal with |- mreal _ _ ?t _ => change t with (@IRet astate (option sptr * astate) (Some (p6 A n A3), A6 A n A3 m)) end.
apply mreal_IRet.
set (E := E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 g) (xr_of regs6)).
assert (SV : forall off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
word_at src0segs mem6 (sp - - off) (getr regs r)).
{ intros off r Hin k Hk. replace (sp - - off + Z.of_nat k) with (sp + off + Z.of_nat k) by lia. apply STK; assumption. }
assert (HS6 : st_ok src0segs E ss_ret1 (mkst regs6 (Z_to_bv 64 RA_AM) mem6 (seg_rom src0segs))).
{ subst E. apply (st_ok_ret1 regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 g) (xr_of regs6) regs6 mem6).
- repeat split; reflexivity.
- exact R2. - exact R3. - exact R4. - exact R8. - exact R9. - exact R18.
- rewrite R19, Hn'. reflexivity.
- exact R20.
- apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit. - apply R2x; bvlit.
- fold sp. lia.
- exact Kws.
- exact (SV (-48) 20%bv ltac:(cbn; tauto)).
- exact (SV (-40) 19%bv ltac:(cbn; tauto)).
- exact (SV (-32) 18%bv ltac:(cbn; tauto)).
- exact (SV (-24) 9%bv ltac:(cbn; tauto)).
- exact (SV (-16) 8%bv ltac:(cbn; tauto)).
- exact (SV (-8) 1%bv ltac:(cbn; tauto)).
- intros k Hk. rewrite <- B_lock. apply (st_lock _ _ (mid_statics _ _ _ _ _ MID3)). exact Hk.
- rewrite <- B_nl. apply (st_needlocks _ _ (mid_statics _ _ _ _ _ MID3)).
- exact Kwe.
- rewrite Hn'. lia.
- lia.
- exact Haimg.
- exact R10.
- rewrite Ug. lia. - rewrite Ug. lia. - rewrite Ug. exact Galign. - rewrite Ug. exact Himg_g.
- rewrite Ug. intros x Hx. apply present_writable. apply MPRES. lia.
- rewrite Ug. lia.
- intros i Hi. apply Z6. lia.
- intros x Hx. apply present_writable. apply P6. lia.
- intros k Hk. rewrite <- B_segs. pose proof (CTR6 k Hk) as C. rewrite B_ctx in C. unfold CTX_mmap_counter in C. exact C.
- lia.
- intros x Hx. rewrite <- B_segs. apply (so_ctx_rw _ (mc_syms _ _ _ _ _ M)). rewrite B_ctx. unfold CTX, CTX_SIZE in *. lia. }
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_enframe E ss_ret1 ss_enf RS_running);
[exact Hh3 | exact Hlz3 | exact HS6 | apply run_ret1 |].
intros ms9 HS9 HF9. cbn [ms_mem] in HF9.
set (mem9 := ms_mem ms9) in *. set (regs9 := ms_regs ms9).
assert (W9 : forall x, 0 <= x < 2 ^ 64 -> ~ wr1 regs a (Z_to_bv 64 g) x -> mem9 (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x)).
{ intros x Hx Hnw. specialize (HF9 (Z_to_bv 64 x)). rewrite u64_of_Z in HF9 by exact Hx. apply HF9.
intros W. apply Hnw. eapply (in_wrange_ret1 regs); [apply sk_ret1 | exact W]. }
sym_reg HS9 (1%bv : reg) as R9_1. sym_reg HS9 (2%bv : reg) as R9_2. sym_reg HS9 (10%bv : reg) as R9_10.
sym_reg HS9 (11%bv : reg) as R9_11. sym_reg HS9 (12%bv : reg) as R9_12.
pose proof (st_ok_reg src0segs E ss_enf ms9 13 HS9) as R9_13. eval_sr_get_in R9_13. cbn [sv_denot] in R9_13.
subst E. cbn [ew E_mi] in R9_1, R9_2, R9_10, R9_11, R9_12, R9_13. rewrite Hn in R9_12.
fold regs9 in R9_1, R9_2, R9_10, R9_11, R9_12, R9_13.
set (ctrw := getr regs9 13) in *.
rewrite (u64_of_Z (st_mmap_counter A)) in R9_13 by lia. rewrite !Z.add_0_r in R9_13.
set (E := E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 g) (xr_of regs6)) in HS9.
st_chunk HS9 0%nat (mkChunk 0 (CVal 8 (SOff 35 0))) CK_map. subst E. cbn [ew E_mi] in CK_map.
set (E := E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 g) (xr_of regs6)) in HS9, CK_map.
st_chunk HS9 1%nat (mkChunk 16 (CVal 8 (SOff 34 0))) CK_m16. st_chunk HS9 1%nat (mkChunk 24 (CVal 4 (SLit 0))) CK_m24.
st_chunk HS9 1%nat (mkChunk 28 (CVal 4 (SLit 0))) CK_m28.
st_chunk HS9 1%nat (mkChunk 32 (CVal 8 (SAlu ALU_OR (SAlu ALU_AND (SOff 10 4115) (SLit (-2048))) (SLit 4064)))) CK_m32.
st_chunk HS9 5%nat (mkChunk (CTX + 12) (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 33 0)) (SLit 1)))) CK_ctr.
subst E. cbn [ew E_mi] in CK_m16, CK_m24, CK_m28, CK_m32, CK_ctr. rewrite !Ug in CK_m16. rewrite !Ug in CK_m24. rewrite !Ug in CK_m28. rewrite !Ug in CK_m32.
set (E := E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 g) (xr_of regs6)) in HS9, CK_map, CK_m16, CK_m24, CK_m28, CK_m32, CK_ctr.
fold mem9 in CK_map, CK_m16, CK_m24, CK_m28, CK_m32, CK_ctr.
assert (MAPW : word_mem src0segs mem9 (bv_unsigned a) g).
{ rewrite <- (Z.add_0_r (bv_unsigned a)). eapply (chunk_word_mem src0segs E); [exact CK_map | subst E; cbn [sv_denot ew E_mi]; rewrite Ug, Z.add_0_r; reflexivity | lia]. }
assert (M16 : word_mem src0segs mem9 (g + 16) (bv_unsigned a)).
{ eapply (chunk_word_mem src0segs E); [exact CK_m16 | subst E; cbn [sv_denot ew E_mi]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia]. }
assert (M24 : forall k, (k < 4)%nat -> mbyte src0segs mem9 (g + 24 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 4 k))).
{ intros k Hk. eapply (chunk_bytes_cval_exact src0segs E _ _ _ 4 (SLit 0) 0 CK_m24 eq_refl ltac:(lia) k Hk). }
assert (M28 : forall k, (k < 4)%nat -> mbyte src0segs mem9 (g + 28 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 0 4 k))).
{ intros k Hk. eapply (chunk_bytes_cval_exact src0segs E _ _ _ 4 (SLit 0) 0 CK_m28 eq_refl ltac:(lia) k Hk). }
pose proof (maplen_facts n (proj1 Hrange) (proj2 Hrange)) as [MPL [MP32 MP51]]. fold (dlen n) in MPL.
pose proof (e_facts n A3 (proj1 Hrange) m HI3 (proj2 Hrange)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
unfold IB, UNIT in F2, F8, F9, D3, D4. rewrite PG in F6, MPL.
set (mp := YN2f.maplen n) in *.
assert (M32 : word_mem src0segs mem9 (g + 32) (bits_enc 0 63 mp)).
{ eapply (chunk_word_mem src0segs E); [exact CK_m32 | | pose proof (bits_nonneg 0 63 mp); pose proof (bits_lt64 0 63 mp); lia].
subst E; cbn [sv_denot ew E_mi]. rewrite Hn'. subst mp. unfold YN2f.maplen, dlen, dm_len. rewrite <- PG. apply bits_word. lia. }
assert (CTR9 : forall k, (k < 4)%nat -> mbyte src0segs mem9 (CTX + 12 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (ctr5 A3) 4 k))).
{ intros k Hk. rewrite <- (Z.add_0_l (CTX + 12)). eapply (chunk_bytes_cval src0segs E _ 0 (CTX + 12) 4 _ (ctr5 A3) CK_ctr); [|exact Hk].
subst E; cbn [sv_denot ew E_mi]. rewrite (u64_of_Z (st_mmap_counter A)) by lia. rewrite Z.add_0_r.
change (8 * Z.of_N 4) with 32. rewrite (ctr_chunk_mod (st_mmap_counter A) Rctr).
unfold ctr5, dm_ctr. destruct FR3 as (_ & _ & _ & _ & EC). rewrite EC. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (dA2_fields A n))))))).
change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity. }
set (ctr64 := bv_unsigned ctrw).
assert (Hc64 : 0 <= ctr64 < 2 ^ 64) by (subst ctr64; apply u64_range).
assert (CTR64 : Z.land ctr64 255 = Z.land (ctr5 A3) 255).
{ rewrite !land255_mod. apply mod32_mod256. subst ctr64. rewrite R9_13. rewrite (ctr_word_mod (st_mmap_counter A) Rctr).
unfold ctr5, dm_ctr. destruct FR3 as (_ & _ & _ & _ & EC). rewrite EC. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (dA2_fields A n))))))).
change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity. }
destruct (enframe_bridge n A3 ctr64 (bv_unsigned a) MP32 F8 F1 F3 (proj1 Hc64) CTR64) as (BST & BOFF & BSTA & BQ & BEND & BRES & BCODE & BH16). fold mp in BST, BOFF, BSTA, BQ, BEND, BRES, BCODE, BH16.
assert (Z9 : forall i, 8 <= i < dlen n -> mbyte src0segs mem9 (bv_unsigned a + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold mbyte. rewrite W9; [fold (mbyte src0segs mem6 (bv_unsigned a + i)); apply Z6; lia | lia |].
destruct (GB (bv_unsigned a + i) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
intros [[Hs|Hs]|[Hm|[Hgg|Hc]]]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply Q3; apply src0_errno_img; exact Hs | lia | rewrite Ug in Hgg; lia
| apply Q3; apply src0_rwseg_img; unfold CTX, src0_D_malloc_context in Hc; lia]. }
assert (P9 : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present mem9 x).
{ intros x Hx. destruct (GB x Hx) as (Q1 & Q2 & Q3 & Q4). destruct (Z_lt_le_dec x (bv_unsigned a + 8)).
- pose proof (MAPW (Z.to_nat (x - bv_unsigned a)) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia. replace (bv_unsigned a + (x - bv_unsigned a)) with x in Hb by lia.
rewrite mbyte_off_img in Hb; [eexists; exact Hb | lia | intros Hi; apply Q3; apply in_img1_img; exact Hi].
- pose proof (Z9 (x - bv_unsigned a) ltac:(lia)) as Hb. replace (bv_unsigned a + (x - bv_unsigned a)) with x in Hb by lia.
rewrite mbyte_off_img in Hb; [eexists; exact Hb | lia | intros Hi; apply Q3; apply in_img1_img; exact Hi]. }
destruct (enframe_steps mem9 (seg_rom src0segs) g (bv_unsigned a) 0 n ctr64 0 63 mp 0 (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) M32 M16
ltac:(intros Hm1; exfalso; unfold mapped1 in Hm1; rewrite (proj2 (Z.eqb_neq mp 0)) in Hm1 by lia; discriminate Hm1)
Hc64 ltac:(lia) ltac:(rewrite BST; lia) ltac:(rewrite BST; lia) ltac:(rewrite BST; lia)
ltac:(rewrite BSTA; replace (bv_unsigned a + 16 - 4) with (bv_unsigned a + 12) by lia; apply Z9; lia)
ltac:(rewrite BSTA; replace (bv_unsigned a + 16 - 3) with (bv_unsigned a + 13) by lia; apply Z9; lia)
ltac:(rewrite BSTA; replace (bv_unsigned a + 16 - 2) with (bv_unsigned a + 14) by lia; apply Z9; lia)
ltac:(rewrite BSTA; replace (bv_unsigned a + 16 - 1) with (bv_unsigned a + 15) by lia; apply Z9; lia)
ltac:(rewrite BSTA, BEND; intros x Hx; apply present_writable; apply P9; lia)
ltac:(rewrite BSTA, BST; lia)
regs9 R9_10 R9_11 R9_12 ltac:(subst ctr64; symmetry; apply Z_to_bv_bv_unsigned))
as (regsF & MS & RA0 & RF).
rewrite BQ in RA0.
rewrite (st_ok_mkst src0segs E ss_enf ms9 HS9 eq_refl). rewrite ss_enf_pc. fold regs9.
change (ms_mem ms9) with mem9.
eapply (SR_msteps src0segs _ _ md3 _ Hh3 Hlz3 MS). apply SR_ret.
intros MP. destruct MP as [HI6 MP]. cbn [fst snd] in HI6, MP.
destruct MP as (g' & am' & idx' & off' & _ & (l1 & l2 & E1 & E2)).
assert (UB6 : user_blocks (A6 A n A3 m) = map fst l1 ++ (p6 A n A3, n) :: map fst l2 /\ user_blocks A = map fst l1 ++ map fst l2).
{ rewrite (user_blocks_ublist (A6 A n A3 m) (proj1 (inv_keys HI6))), (user_blocks_ublist A (proj1 (inv_keys HW))), E1, E2, !map_app. cbn [map fst]. auto. }
rewrite R9_1. pose proof Hret as RET. unfold YK0s.ret_ok in RET. rewrite RET.
set (b0 := Z_to_bv 8 0) in *.
set (memF := YN04.memF mem9 (bv_unsigned a) 0 n ctr64 0 mp 0 b0 b0 b0) in *.
assert (EH1 : 0 <= 0 < 32) by lia. assert (EH2 : 0 <= 63 < 64) by lia. assert (EH3 : 0 <= mp < 2 ^ 52) by lia.
assert (EH6 : 0 <= n /\ n + 4 <= stride 0 mp 0) by (rewrite BST; lia).
assert (EH7 : 16 <= bv_unsigned a /\ bv_unsigned a + 16 + stride 0 mp 0 * 0 + stride 0 mp 0 <= 2 ^ 63) by (rewrite BST; lia).
assert (EH8 : stride 0 mp 0 * 0 + (stride 0 mp 0 - 4 - n) < 2 ^ 20) by (rewrite BST; lia).
assert (EC4 : mbyte src0segs mem9 (start (bv_unsigned a) 0 0 mp 0 - 4) = Some (Z_to_bv 8 0)).
{ rewrite BSTA. replace (bv_unsigned a + 16 - 4) with (bv_unsigned a + 12) by lia. apply Z9. lia. }
pose proof (memF_frame mem9 (bv_unsigned a) 0 n ctr64 0 63 mp 0 b0 b0 b0 EH1 EH2 EH3 Hc64 EH1 EH6 EH7 EH8) as MFR.
pose proof (memF_hdr mem9 (bv_unsigned a) 0 n ctr64 0 63 mp 0 b0 b0 b0 EH1 EH2 EH3 Hc64 EH1 EH6 EH7 EH8 EC4) as MHD.
pose proof (memF_tail mem9 (bv_unsigned a) 0 n ctr64 0 63 mp 0 b0 b0 b0 EH1 EH2 EH3 Hc64 EH1 EH6 EH7 EH8) as MTL.
pose proof (memF_present mem9 (bv_unsigned a) 0 n ctr64 0 63 mp 0 b0 b0 b0 EH1 EH2 EH3 Hc64 EH1 EH6 EH7 EH8) as MPR.
pose proof (memF_writable mem9 (bv_unsigned a) 0 n ctr64 0 63 mp 0 b0 b0 b0 EH1 EH2 EH3 Hc64 EH1 EH6 EH7 EH8) as MWR.
fold memF in MFR, MHD, MTL, MPR, MWR.
unfold written in MFR. rewrite !BSTA, !BQ, !BEND in MFR. rewrite !BSTA, !BQ, !BOFF, !BCODE, !BH16 in MHD. rewrite !BQ, !BEND, !BRES in MTL.
set (q6 := bv_unsigned a + UNIT + UNIT * e_off n A3) in *.
assert (UQ : q6 = bv_unsigned a + 16 + 16 * e_off n A3) by (subst q6; unfold UNIT; lia).
assert (F0 : forall x, 0 <= x < 2 ^ 64 ->
~ ((sp - ALLOC_STACK <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4)) ->
~ (ms_ctx B + CTX_mmap_counter <= x < ms_ctx B + CTX_mmap_counter + 4) ->
~ (g + 16 <= x < g + 40) -> ~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> memF (Z_to_bv 64 x) = mem6 (Z_to_bv 64 x)).
{ intros x Hx Hns Hnc Hng Hna. rewrite MFR; [| exact Hx | lia]. apply W9; [exact Hx|].
intros [Hs|[Hm|[Hgg|Hc]]]; [apply Hns; unfold scratch, spZ in Hs; fold sp in Hs; rewrite B_errno in Hs; unfold ALLOC_STACK; exact Hs | lia | rewrite Ug in Hgg; lia
| apply Hnc; rewrite B_ctx; unfold CTX_mmap_counter, CTX in *; lia]. }
assert (F1a : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> present memF x).
{ intros x Hx. destruct (P9 x Hx) as [b Hb]. pose proof (u64_range a).
destruct (memF (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; exact Eb|]. exfalso. apply (MPR (Z_to_bv 64 x)); [rewrite Hb; discriminate | exact Eb]. }
assert (F1p : forall x, 0 <= x < alloc_ceiling -> ~ in_img B x -> present mem6 x -> present memF x).
{ intros x Hxc Hni [b Hb]. assert (Hx : 0 <= x < 2 ^ 64) by lia.
assert (P9x : mem9 (Z_to_bv 64 x) <> None).
{ destruct (Z_lt_le_dec x (bv_unsigned a)) as [C1|C1]; [|destruct (Z_lt_le_dec x (bv_unsigned a + dlen n)) as [C2|C2]; [destruct (P9 x ltac:(lia)) as [b' Hb']; rewrite Hb'; discriminate|]].
all: destruct (Z_lt_le_dec x (g + 16)) as [C3|C3]; [|destruct (Z_lt_le_dec x (g + 40)) as [C4|C4];
[destruct (writable_off_img_present mem9 x Hx ltac:(intros Hi; apply Hni; apply in_img1_img; exact Hi)
ltac:(replace x with (bv_unsigned (Z_to_bv 64 g) + (x - g)) by (rewrite Ug; lia); subst mem9; st_writable HS9 1%nat (x - g); cbn [r_wlo r_whi]; lia))
as [b' Hb']; rewrite Hb'; discriminate|]].
all: rewrite W9; [rewrite Hb; discriminate | exact Hx |].
all: intros [[Hs|Hs]|[Hm|[Hgg|Hc]]]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply Hni; apply src0_errno_img; exact Hs | lia | rewrite Ug in Hgg; lia
| apply Hni; apply src0_rwseg_img; unfold CTX, src0_D_malloc_context in Hc; lia]. }
destruct (memF (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; exact Eb|]. exfalso. exact (MPR (Z_to_bv 64 x) P9x Eb). }
assert (MBE : forall (m1 m2 : word -> option byte) x, m1 (Z_to_bv 64 x) = m2 (Z_to_bv 64 x) -> mbyte src0segs m1 x = mbyte src0segs m2 x)
by (intros m1 m2 x E0; unfold mbyte; rewrite E0; reflexivity).
assert (NW1 : forall x, 0 <= x < alloc_ceiling -> ~ in_img B x -> ~ (bv_unsigned a <= x < bv_unsigned a + 8) -> ~ (g + 16 <= x < g + 40) ->
~ wr1 regs a (Z_to_bv 64 g) x).
{ intros x H1 H2 H3 H4 [[Hs|Hs]|[Hm|[Hgg|Hc]]]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; apply H2; apply src0_errno_img; exact Hs | lia | rewrite Ug in Hgg; lia
| apply H2; apply src0_rwseg_img; unfold CTX, src0_D_malloc_context in Hc; lia]. }
assert (F96 : forall x, 0 <= x < alloc_ceiling -> ~ in_img B x -> ~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> ~ (g + 16 <= x < g + 40) ->
mbyte src0segs memF x = mbyte src0segs mem6 x).
{ intros x H1 H2 H3 H4. rewrite (MBE memF mem9 x) by (apply MFR; lia). apply MBE. apply W9; [lia|]. apply NW1; try assumption. lia. }
assert (F9g : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> ~ (bv_unsigned a + 12 <= x < bv_unsigned a + 16) -> ~ (q6 - 4 <= x < q6) -> ~ (q6 + n <= x < bv_unsigned a + dlen n - 4) ->
mbyte src0segs memF x = mbyte src0segs mem9 x).
{ intros x H1 H2 H3 H4. apply MBE. apply MFR; lia. }
assert (LB1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v).
{ intros v Hv. unfold le_byte. cbn [Nat.mul Z.of_nat Z.mul Pos.mul]. rewrite Z.shiftr_0_r. rewrite (Z.mod_small v) by lia. apply Z.mod_small. lia. }
assert (Epadd : forall d, loc_addr L3 (LMem (padd m d)) = g + d) by (intros d; unfold g; destruct m; cbn; lia).
assert (Er0 : forall p, prid p = YN2c.r0 A -> loc_addr L3 (LMem p) = bv_unsigned a + poff p) by (intros [pr po] Hp; cbn in Hp |- *; subst pr; rewrite L3r0; reflexivity).
assert (NEWOK : forall c, In c (new_cells A n A3 m ++ group_tail_cells (YN2f.am6 A n A3)) -> cell_mem B L3 memF c).
{ intros c Hc. apply (newc_cases A n A3 (proj1 Hrange) m HI3 Mm (proj2 Hrange)) in Hc. unfold newc_spec in Hc. fold mp in Hc.
destruct Hc as [-> | [(d & w & v & -> & Hd) | (p & w & v & -> & Hpr & Hoff)]].
-   unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num loc_addr]. rewrite (mid_ctx _ _ _ _ _ MID3), B_ctx, B_segs. unfold CTX_mmap_counter. intros k Hk.
rewrite (MBE memF mem9).
+ apply CTR9. exact Hk.
+ apply MFR; [unfold CTX, src0_D_malloc_context; lia|]. intros W. apply (NI (CTX + 12 + Z.of_nat k)); [lia | apply src0_rwseg_img; unfold CTX, src0_D_malloc_context; lia].
-
unfold cell_mem. cbn [mc_loc mc_w mc_val]. rewrite Epadd, B_segs.
assert (GW : forall k, (k < 8)%nat -> d = 0 \/ d = 8 -> mbyte src0segs memF (g + d + Z.of_nat k) = mbyte src0segs mem6 (g + d + Z.of_nat k)).
{ intros k Hk Hd2. apply F96; [lia | apply Gimg; lia | lia | lia]. }
assert (GW2 : forall k, (k < 24)%nat -> mbyte src0segs memF (g + 16 + Z.of_nat k) = mbyte src0segs mem9 (g + 16 + Z.of_nat k)).
{ intros k Hk. apply MBE. apply MFR; [lia|]. lia. }
destruct Hd as [(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]]]]; cbn [sval_num].
+ intros k Hk. rewrite GW by (auto; lia). pose proof OC1 as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite Epadd, B_segs in C. apply C. exact Hk.
+ intros k Hk. rewrite GW by (auto; lia). pose proof OC2 as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val sval_num] in C. rewrite Epadd, B_segs in C. apply C. exact Hk.
+ intros k Hk. cbn [loc_addr]. rewrite L3r0, Z.add_0_r. replace (g + 16 + Z.of_nat k) with (g + 16 + Z.of_nat (k + 0)) by lia. rewrite (GW2 (k + 0)%nat) by lia.
replace (g + 16 + Z.of_nat (k + 0)) with (g + 16 + Z.of_nat k) by lia. apply M16. exact Hk.
+ intros k Hk. replace (g + 24 + Z.of_nat k) with (g + 16 + Z.of_nat (k + 8)) by lia. rewrite GW2 by lia.
replace (g + 16 + Z.of_nat (k + 8)) with (g + 24 + Z.of_nat k) by lia. apply M24. exact Hk.
+ intros k Hk. replace (g + 28 + Z.of_nat k) with (g + 16 + Z.of_nat (k + 12)) by lia. rewrite GW2 by lia.
replace (g + 16 + Z.of_nat (k + 12)) with (g + 28 + Z.of_nat k) by lia. apply M28. exact Hk.
+ intros k Hk. replace (g + 32 + Z.of_nat k) with (g + 16 + Z.of_nat (k + 16)) by lia. rewrite GW2 by lia.
replace (g + 16 + Z.of_nat (k + 16)) with (g + 32 + Z.of_nat k) by lia. apply M32. exact Hk.
-
unfold cell_mem. cbn [mc_loc mc_w mc_val]. rewrite (Er0 p Hpr), B_segs. cbv zeta in Hoff.
destruct MHD as (MH1 & MH2 & MH3 & MH4 & MH5 & MH6). destruct MTL as (MT1 & MT2 & MT3).
destruct Hoff as [(Eo & -> & ->)|[(Eo & -> & ->)|[(Eo & -> & ->)|[(Eo & -> & ->)|[(Eo & -> & ->)|[(Ne & Eo & -> & ->)|[(Ne & Eo & -> & ->)|[(Ne & Eo & -> & ->)|[(Eo & -> & ->)|[(Hr0 & Eo & -> & ->)|[(Hr5 & Eo & -> & ->)|(Hr5 & Eo & -> & ->)]]]]]]]]]]];
rewrite Eo; cbn [sval_num].
+   intros k Hk. fold g. rewrite F9g by lia. rewrite Z.add_0_r. apply MAPW. exact Hk.
+   intros k Hk. rewrite F9g by lia. rewrite <- Z.add_assoc. rewrite Z9 by lia. unfold le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
+   intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + 12) with (bv_unsigned a + 16 - 4) by lia. rewrite MH1. rewrite LB1 by lia. reflexivity.
+   intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + 13) with (bv_unsigned a + 16 - 3) by lia. rewrite MH2.
rewrite LB1 by (destruct (e_off n A3 =? 0); lia). destruct (e_off n A3 =? 0); [rewrite Z.mul_comm|]; reflexivity.
+   intros k Hk. replace (bv_unsigned a + 14 + Z.of_nat k) with (bv_unsigned a + 16 - 2 + Z.of_nat k) by lia. rewrite MH3 by exact Hk.
destruct (Z.eqb_spec (e_off n A3) 0) as [E0|E0]; [rewrite E0|]; reflexivity.
+ intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + (16 + 16 * e_off n A3 - 4)) with (q6 - 4) by lia. rewrite MH4. reflexivity.
+ intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + (16 + 16 * e_off n A3 - 3)) with (q6 - 3) by lia. rewrite MH5. rewrite LB1 by lia. rewrite Z.mul_comm. reflexivity.
+ intros k Hk. replace (bv_unsigned a + (16 + 16 * e_off n A3 - 2) + Z.of_nat k) with (q6 - 2 + Z.of_nat k) by lia. apply MH6. exact Hk.
+   intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. rewrite F9g by lia. replace (bv_unsigned a + (dlen n - 4)) with (bv_unsigned a + (dlen n - 4)) by lia.
rewrite Z9 by lia. rewrite LB1 by lia. reflexivity.
+ intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + (16 + 16 * e_off n A3 + n)) with (q6 + n) by lia. rewrite (MT1 Hr0). rewrite LB1 by lia. reflexivity.
+ intros k Hk. replace (bv_unsigned a + (dlen n - 8) + Z.of_nat k) with (bv_unsigned a + dlen n - 4 - 4 + Z.of_nat k) by lia. apply (MT3 Hr5). exact Hk.
+ intros k Hk. destruct k; [|lia]. rewrite Z.add_0_r. replace (bv_unsigned a + (dlen n - 9)) with (bv_unsigned a + dlen n - 4 - 5) by lia. rewrite (MT2 Hr5). rewrite LB1 by lia. reflexivity. }
pose proof (D3_post B L A mem md a n L3 A3 mem6 md3 m sp memF (map fst l1) (map fst l2) MX Hrange GR src0_ENC src0_ENS src0_ERRIMG src0_SNC
MID3 LE3 FR3 UB3 HI3 EU3 Km Mm HB3 HA3 ltac:(unfold ALLOC_STACK; lia) F0 F1a F1p NEWOK HI6 UB6) as MX6.
assert (OWNA : forall x, ms_ctx B <= x < ms_ctx B + CTX_SIZE -> owned B L A x).
{ intros x Hx. left. split.
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. rewrite (mc_ctx _ _ _ _ _ M). lia.
- intros ([bp bn] & Hb & Hbx). cbn [fst snd] in Hbx.
destruct (OLDB bp bn (x - loc_addr L (LMem bp)) Hb ltac:(lia)) as (EL & _ & NIx & _).
apply NIx. rewrite EL. replace (loc_addr L (LMem bp) + (x - loc_addr L (LMem bp))) with x by lia. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). exact Hx. }
assert (NONMAP : forall x, in_nonmap_region L3 A3 x -> 4096 <= x < alloc_ceiling /\ ~ in_img B x).
{ intros x ((k & rg & Hk & Hl & Hkind & Hx) & _). pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID3) k rg Hk Hl) as (_ & Q1 & Q2 & Q3).
pose proof (reg_lo_le rg). split; [lia|]. apply Q3. lia. }
assert (FRall : forall x, 0 <= x < 2 ^ 64 -> (alloc_ceiling <= x \/ in_img B x) -> ~ owned B L A x -> ~ scratch B regs x ->
memF (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx Hhi Hno Hns.
assert (Hna : ~ (bv_unsigned a <= x < bv_unsigned a + dlen n)) by (intros Hin; apply (NI x Hin); destruct Hhi as [Hhi|Hhi]; [lia | exact Hhi]).
assert (Hng : ~ (g <= x < g + 40)) by (intros Hin; apply (Gimg x Hin); destruct Hhi as [Hhi|Hhi]; [lia | exact Hhi]).
rewrite MFR; [| exact Hx | lia]. rewrite W9; [| exact Hx |].
2:{ intros [Hs|[Hm|[Hgg|Hc]]]; [exact (Hns Hs) | lia | rewrite Ug in Hgg; lia | apply Hno; apply OWNA; rewrite B_ctx; unfold CTX, CTX_SIZE in *; lia]. }
apply FR6; [exact Hx | exact Hns | intros Hc; apply Hno; apply OWNA; exact Hc | intros Hnm; destruct (NONMAP x Hnm) as [Q1 Q2]; destruct Hhi as [Hhi|Hhi]; [lia | exact (Q2 Hhi)] | exact Hna]. }
exists L3, regsF, memF, md3. split; [reflexivity|]. split.
2:{ cbn [fst snd]. split; [rewrite RA0; unfold ptr_addr; rewrite P6A; reflexivity|]. split; [unfold ptr_addr; rewrite P6A; lia|]. split.
- exists (map fst l1), (map fst l2). exact UB6.
-   intros _ i Hi. unfold ptr_addr. rewrite P6A. fold q6. rewrite B_segs.
rewrite F9g by lia. replace (q6 + i) with (bv_unsigned a + (q6 - bv_unsigned a + i)) by lia. apply Z9. lia. }
split; [exact MX6|]. split; [exact HI6|]. split; [apply (bounded_A6 A n A3 m Km Mm HB3)|].
split; [exact (layout_le_A3 L A a n L3 (proj1 Hrange) LE3)|].
split.
{ intros p k Hin _. destruct (block_region A p k HW Hin) as (kk & o & rg & -> & Hr & _). unfold ptr_addr. cbn [loc_addr].
rewrite (L3old kk (region_of_lt A kk rg Hr)). reflexivity. }
split.
{
intros r Hr. rewrite RF.
- revert r Hr. eapply (regs_preserved_sym regs); [apply (proj1 enf_checks) | exact HS9 | exact Htp].
- unfold eclob. unfold callee_saved in Hr. intros [E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|[E0|E0]]]]]]]]]];
apply (f_equal bv_unsigned) in E0; rewrite Z_to_bv_unsigned in E0; unfold bv_wrap in E0; change (bv_modulus 5) with 32 in E0;
rewrite Z.mod_small in E0 by lia;
match type of E0 with _ = bv_unsigned ?l => let v := eval vm_compute in (bv_unsigned l) in change (bv_unsigned l) with v in E0 end; lia. }
split; [destruct VM3 as [vm3 E3]; exists vm3; rewrite E3; unfold md1, mmap_model; apply with_vmmaps_twice|].
split.
{ intros x Hhi Hno _ Hns _.
assert (Hx : 0 <= x < 2 ^ 64) by (destruct Hhi as [Hhi|Hhi]; [lia | apply src0_img_range in Hhi; lia]).
unfold mbyte, writable_at, wview. rewrite B_segs. rewrite (FRall x Hx ltac:(destruct Hhi as [Hhi|Hhi]; [left; lia | right; exact Hhi]) Hno Hns). tauto. }
split.
{ intros p k i Hin _ Hi. destruct (OLDB p k i Hin Hi) as (EL & OK & NIx & NG & NNM). destruct OK as (O1 & O2 & O3 & O4).
unfold ptr_addr. rewrite <- EL. rewrite B_segs. rewrite F96; [| lia | exact NIx | exact O4 | intros Hg2; apply NG; lia].
apply MBE. apply FR6; [lia | | | exact NNM | exact O4].
- intros [Hs|Hs]; [unfold spZ, ALLOC_STACK in Hs; fold sp in Hs; lia | rewrite B_errno in Hs; exact (O3 Hs)].
- intros Hc. apply NIx. apply (so_ctx_img _ (mc_syms _ _ _ _ _ M)). exact Hc. }
intros x Hsx. apply MWR. eapply (scratch_writable_sym regs); [apply (proj2 enf_checks) | exact HS9 |].
unfold scratch, spZ, ALLOC_STACK in Hsx. rewrite B_errno in Hsx. exact Hsx.
Qed.
Lemma granted_branch : forall L A regs mem md n regs2 mem2 (a : word),
call_pre B (MRx B) L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2 ^ 62 ->
let E0 := E_entry regs A (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0) in
regs_ok E0 (ss_regs ss_mmap) regs2 -> mem_ok src0segs E0 mem2 (ss_mem ss_mmap) -> facts_ok E0 (ss_facts ss_mmap) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> mem2 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
grant_ok (Z_to_bv 64 0) md a (dlen n) = true ->
mreal src0segs (mkCfg (mkst (regupd regs2 10 a) (v_addi (Z_to_bv 64 (ss_pc ss_mmap)) 4) (apply_zeros mem2 [(a, Z_to_bv 64 (dlen n))]) (seg_rom src0segs))
(md1 md a (dlen n)))
(dm_rest n A)
(fun r c' => malloc_post [] U0 A n r -> malloc_leaf B (MRx B) L A regs mem md n r c').
Proof.
intros L A regs mem md n regs2 mem2 a PRE Hn Hrange E0 HR2 HM2 HG2 FR2 GR.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Hauxv).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range a) as Ua.
pose proof (dlen_facts n (proj1 Hrange)) as (D1 & D2 & D3 & D4 & D5).
pose proof (grant_facts B L A mem md a (dlen n) MX (conj D1 D2) GR) as (Gal & Gpos & Gceil & _ & _).
pose proof (inv_ctx HW) as (Lact & Lus & Luseq & Lbo & Uus & Uuseq & Ubo & Rseq & Rctr & _).
assert (HT : MMAP_THRESHOLD = 131052) by reflexivity. assert (PG : PGSZ = 4096) by reflexivity.
assert (Hn' : bv_unsigned (getr regs 10) = n) by (rewrite Hn; apply u64_of_Z; lia).
set (sp := bv_unsigned (getr regs 2)) in *. unfold spZ in *. fold sp in Hal, Hceil, Hsp63, Hstk. unfold ALLOC_STACK in Hceil, Hstk.
assert (NI : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> ~ in_img B x).
{ intros x Hx Hi. exact (new_disjoint_img B L A mem md a (dlen n) MX (dlen_pos n (proj1 Hrange)) GR x Hi Hx). }
assert (Haimg : bv_unsigned a + 131072 <= 0x1f000 \/ 0x51000 <= bv_unsigned a).
{ destruct (Z_lt_le_dec (bv_unsigned a) 0x51000); [left|right; lia].
destruct (Z_lt_le_dec 0x1f000 (bv_unsigned a + 131072)); [|lia]. exfalso.
apply (NI (Z.max (bv_unsigned a) 0x1f000)); [lia|]. apply src0_rwseg_img. lia. }
assert (Ha4 : 4096 <= bv_unsigned a).
{ rewrite PG in Gal. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)). lia. }
destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
assert (Hh1 : m_halted (md1 md a (dlen n)) = None) by (unfold md1; rewrite mmap_model_halted; exact Hh).
assert (Hlz1 : m_vm_lazy (md1 md a (dlen n)) = []) by (unfold md1; rewrite mmap_model_lazy; exact Hlz).
set (E := E_entry regs A a (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0)).
assert (HSg : st_ok src0segs E ss_granted
(mkst (regupd regs2 10 a) (v_addi (Z_to_bv 64 (ss_pc ss_mmap)) 4) (apply_zeros mem2 [(a, Z_to_bv 64 (dlen n))]) (seg_rom src0segs))).
{ assert (Haimg2 : bv_unsigned a + dlen n <= 0x1f000 \/ 0x51000 <= bv_unsigned a).
{ destruct (Z_lt_le_dec (bv_unsigned a) 0x51000); [left|right; lia].
destruct (Z_lt_le_dec 0x1f000 (bv_unsigned a + dlen n)); [|lia]. exfalso.
apply (NI (Z.max (bv_unsigned a) 0x1f000)); [lia|]. apply src0_rwseg_img. lia. }
subst E. unfold E_entry. apply (st_ok_granted regs (st_seq A) (st_mmap_counter A) (useq_of A) (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0));
try assumption; try (fold sp; lia).
intros x Hx. rewrite <- B_segs. apply (so_ctx_rw _ (mc_syms _ _ _ _ _ M)). rewrite B_ctx. unfold CTX, CTX_SIZE in *. lia. }
rewrite dm_rest_eq.
eapply (mreal_SR_pre src0segs _ _ _
(fun c5 => exists ms5, c5 = mkCfg ms5 (md1 md a (dlen n)) /\
((st_seq A = 255 /\ st_ok src0segs E ss_am255 ms5) \/ (st_seq A <> 255 /\ st_ok src0segs E ss_amne ms5)) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ wr_g regs a x -> ms_mem ms5 (Z_to_bv 64 x) = apply_zeros mem2 [(a, Z_to_bv 64 (dlen n))] (Z_to_bv 64 x)))).
{ eapply (run_to_am regs (st_seq A) (st_mmap_counter A) (useq_of A) a (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0));
[exact Hh1 | exact Hlz1 | exact HSg | lia | lia |].
intros ms5 VAR FR5. apply SR_ret. exists ms5. split; [reflexivity|]. split; [exact VAR | exact FR5]. }
intros c5 (ms5 & -> & VAR & FR5).
destruct (am_entry L A regs mem md n mem2 a ms5 PRE Hn Hrange FR2 GR VAR FR5)
as (MID & CPRE & AUX & Kst & K1 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K2x & Kstk & ZB & ZP & Kws & Kwe).
fold sp in K2, Kstk, Kws.
rewrite Kst.
pose proof (AMH [] None U0 (L1 L A a) (dA2 A n) (ms_regs ms5) (ms_mem ms5) (md1 md a (dlen n))
(dA2_inv A n HW (proj1 Hrange)) ltac:(intros ? ? [])
(dA2_ama A n (MRx_ama _ _ _ _ _ MX)) (dA2_bounded A n HB) MID AUX CPRE) as RUN.
change (pc_alloc_meta (ms_pcs B)) with src0_A_alloc_meta in RUN. change (ms_segs B) with src0segs in RUN.
pose proof (mreal_itok _ _ _ _ _ RUN (alloc_meta_facts A n HW (proj1 Hrange))) as RUN2. clear RUN.
eapply mreal_ibind; [exact RUN2|]. clear RUN2.
intros [og A3] c6 [(L3 & regs6 & mem6 & md3 & -> & CPOST & AMA3 & BND3 & RES & RESnz) AMP].
cbn [fst snd] in RES, RESnz, AMA3, BND3.
destruct CPOST as (MID3 & LE3 & PRES & VM3 & FRM & SCW).
destruct AMP as (FR3 & UB3 & AMP). cbn [fst snd] in FR3, UB3, AMP.
assert (FR6 : forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> ~ in_nonmap_region L3 A3 x ->
~ (bv_unsigned a <= x < bv_unsigned a + dlen n) -> mem6 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx Hns Hnc Hnm Hna. rewrite (FRM x Hx Hnc Hnm).
2:{ intros [Hs|Hs]; apply Hns; [left | right; exact Hs]. unfold spZ in Hs |- *. rewrite K2, u64_of_Z in Hs by lia. fold sp. unfold AM_STACK, ALLOC_STACK in *. lia. }
rewrite (FR5 x Hx). 2:{ intros [Hs|[Hc|Hm]]; [exact (Hns Hs) | apply Hnc; rewrite B_ctx; unfold ctxw in Hc; rewrite B_ctx in Hc; unfold CTX_SIZE; lia | lia]. }
rewrite apply_zeros1_out by (rewrite !u64_of_Z by lia; lia). apply FR2; [exact Hx | exact Hns]. }
assert (Usp : bv_unsigned (Z_to_bv 64 (sp - 48)) = sp - 48) by (apply u64_of_Z; lia).
assert (STK6 : forall k off (r : reg), In (off, r) [(-48, 20%bv : reg); (-40, 19%bv : reg); (-32, 18%bv : reg); (-24, 9%bv : reg); (-16, 8%bv : reg); (-8, 1%bv : reg)] ->
(k < 8)%nat -> mbyte src0segs mem6 (sp + off + Z.of_nat k) = Some (byte_of_word (getr regs r) (Z.of_nat k))).
{ intros k off r Hin Hk.
assert (Hoff : -48 <= off <= -8) by (cbn [In] in Hin; destruct Hin as [E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]; injection E1 as <- <-; lia).
unfold mbyte. rewrite (FRM (sp + off + Z.of_nat k)).
- fold (mbyte src0segs (ms_mem ms5) (sp + off + Z.of_nat k)). apply Kstk; assumption.
- lia.
- rewrite B_ctx. unfold CTX, CTX_SIZE, src0_D_malloc_context. lia.
- intros ((kk & rg & Hk2 & Hl & _ & Hx2) & _). pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID3) kk rg Hk2 Hl) as (_ & _ & Q & _). lia.
- unfold call_scratch, spZ. rewrite K2, Usp, B_errno. unfold AM_STACK, ERRNO, src0_tp. lia. }
assert (Kws6 : forall x, sp - 8192 <= x < sp -> writable_at src0segs mem6 x).
{ intros x Hx. destruct (Z_lt_le_dec x (sp - 48 - AM_STACK)) as [Hlt|Hge]; [| destruct (Z_lt_le_dec x (sp - 48)) as [Hlt2|Hge2]].
- unfold writable_at, wview. rewrite (FRM x); [apply Kws; lia | lia | rewrite B_ctx; unfold CTX, CTX_SIZE, src0_D_malloc_context; lia | | ].
+ intros ((kk & rg & Hk2 & Hl & _ & Hx2) & _). pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID3) kk rg Hk2 Hl) as (_ & _ & Q & _). lia.
+ unfold call_scratch, spZ. rewrite K2, Usp, B_errno. unfold AM_STACK, ERRNO, src0_tp in *. lia.
- rewrite <- B_segs. apply SCW. left. unfold spZ. rewrite K2, Usp. lia.
- unfold writable_at, wview. rewrite (FRM x); [apply Kws; lia | lia | rewrite B_ctx; unfold CTX, CTX_SIZE, src0_D_malloc_context; lia | | ].
+ intros ((kk & rg & Hk2 & Hl & _ & Hx2) & _). pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID3) kk rg Hk2 Hl) as (_ & _ & Q & _). lia.
+ unfold call_scratch, spZ. rewrite K2, Usp, B_errno. unfold AM_STACK, ERRNO, src0_tp in *. lia. }
assert (Kwe6 : forall x, ERRNO <= x < ERRNO + 4 -> writable_at src0segs mem6 x).
{ intros x Hx. rewrite <- B_segs. apply SCW. right. rewrite B_errno. exact Hx. }
assert (PR : forall r : reg, callee_saved (bv_unsigned r) -> getr regs6 r = getr (ms_regs ms5) r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply PRES. exact Hr. }
destruct og as [m|].
-
destruct AMP as (HI3 & Km & Mm & EU3).
destruct (D3_pre B L A mem md a n L3 A3 mem6 md3 m) as (_ & _ & _ & _ & _ & GB & _); try assumption.
1-4: first [exact src0_ENC | exact src0_ENS | exact src0_ERRIMG | exact src0_SNC].
assert (M65 : forall x, bv_unsigned a <= x < bv_unsigned a + dlen n -> mem6 (Z_to_bv 64 x) = ms_mem ms5 (Z_to_bv 64 x)).
{ intros x Hx. destruct (GB x Hx) as (Q1 & Q2 & Q3 & Q4). apply FRM; [lia | | exact Q2 |].
- rewrite B_ctx. intros Hc. apply Q3. apply src0_rwseg_img. unfold CTX, src0_D_malloc_context, CTX_SIZE in Hc. lia.
- unfold call_scratch, spZ. rewrite K2, Usp, B_errno. unfold AM_STACK, ERRNO, src0_tp. intros [Hs|Hs]; [lia|]. apply Q3. apply src0_rwseg_img. lia. }
rewrite (dm_k_some n A m A3). rewrite K1.
apply (some_tail L A regs mem md n a L3 A3 regs6 mem6 md3 m PRE Hn Hrange GR MID3 LE3 FR3 UB3 HI3 EU3 Km Mm BND3 AMA3 VM3);
fold sp; try assumption.
+ rewrite (PR 2%bv ltac:(creg)). exact K2.
+ rewrite (PR 3%bv ltac:(creg)). exact K3.
+ rewrite (PR 4%bv ltac:(creg)). exact K4.
+ rewrite (PR 8%bv ltac:(creg)). exact K8.
+ rewrite (PR 9%bv ltac:(creg)). exact K9.
+ rewrite (PR 18%bv ltac:(creg)). exact K18.
+ rewrite (PR 19%bv ltac:(creg)). exact K19.
+ rewrite (PR 20%bv ltac:(creg)). exact K20.
+ intros r Hr. rewrite (PR r ltac:(unfold callee_saved; lia)). apply K2x. exact Hr.
+ intros i Hi. unfold mbyte. rewrite M65 by lia. apply ZB. exact Hi.
+ intros x Hx. destruct (ZP x Hx) as [b Hb]. exists b. rewrite M65 by exact Hx. exact Hb.
-
destruct AMP as [HI3 EU3].
rewrite (dm_k_none n A A3). rewrite K1.
apply (none_tail L A regs mem md n a L3 A3 regs6 mem6 md3 PRE Hn Hrange GR MID3 LE3 FR3 UB3 HI3 EU3 BND3 AMA3 VM3);
fold sp; try assumption.
+ rewrite (PR 2%bv ltac:(creg)). exact K2.
+ rewrite (PR 3%bv ltac:(creg)). exact K3.
+ rewrite (PR 4%bv ltac:(creg)). exact K4.
+ rewrite (PR 8%bv ltac:(creg)). exact K8.
+ rewrite (PR 9%bv ltac:(creg)). exact K9.
+ rewrite (PR 18%bv ltac:(creg)). exact K18.
+ rewrite (PR 19%bv ltac:(creg)). exact K19.
+ rewrite (PR 20%bv ltac:(creg)). exact K20.
+ intros r Hr. rewrite (PR r ltac:(unfold callee_saved; lia)). apply K2x. exact Hr.
Qed.
Theorem malloc_direct_mreal : forall L A regs mem md n,
call_pre B (MRx B) L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2 ^ 62 ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs)) md) (malloc n A)
(malloc_leaf B (MRx B) L A regs mem md n).
Proof.
intros L A regs mem md n PRE Hn Hrange.
pose proof PRE as (MX & HW & HB & Hret & Hal & Hceil & Hsp63 & Hstk & Htp & Herr & Hauxv).
pose proof (MRx_MRc _ _ _ _ _ MX) as M. destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & Hmat).
assert (HT : MMAP_THRESHOLD = 131052) by reflexivity.
assert (Hn' : bv_unsigned (getr regs 10) = n) by (rewrite Hn; apply u64_of_Z; lia).
apply (mreal_by_itok src0segs (malloc n A) _ _ (malloc_post [] U0 A n)).
{ apply (malloc_spec U0 A n); [exact HW | lia | intros r H; exact H]. }
rewrite (malloc_direct_tree n A (proj2 (size_overflow_test n ltac:(lia))) (proj1 Hrange)).
apply mreal_IAsk.
set (E := E_entry regs A (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0)).
pose proof (entry_st_ok L A regs mem md (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0) PRE ltac:(lia)) as HS.
change (st_ok src0segs E ss_mi (mkst regs (Z_to_bv 64 src0_A_malloc) mem (seg_rom src0segs))) in HS.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_mi ss_thr); [exact Hh | exact Hlz | exact HS | apply run_mi |].
clear HS. intros ms1 HS HF1.
apply (st_ok_add_cond_neg src0segs E ss_thr ms1 BC_LTU (SOff 10 0) (SLit 131052)) in HS.
2:{ cbn [sv_denot]. subst E. cbn [ew E_entry E_mi]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hn.
rewrite branch_ltu, !u64_of_Z by lia. apply Z.ltb_ge. lia. }
change (add_cond ss_thr (mkAC (neg_bc BC_LTU) (SOff 10 0) (SLit 131052))) with (add_cond ss_thr C_direct) in HS.
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_thr C_direct) ss_mmap ms1); [exact Hh | exact Hlz | exact HS | apply run_thr |].
clear HS. intros ms2 HS HF2.
apply SR_ret.
destruct (st_ok_ecall_shape src0segs E ss_mmap ms2 HS eq_refl) as (regs2 & mem2 & -> & Hregs2 & Hmem2 & HG2). clear HS.
cbn [ms_mem pend_at] in HF2.
assert (FR2 : forall x, 0 <= x < 2 ^ 64 -> ~ scratch B regs x -> mem2 (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx Hns. rewrite (HF2 (Z_to_bv 64 x)), (HF1 (Z_to_bv 64 x)); [reflexivity| |];
rewrite u64_of_Z by exact Hx; intros W; apply Hns;
[eapply (in_wrange_scratch E regs _ x sk_mi); [|exact W] | eapply (in_wrange_scratch E regs _ x sk_thr); [|exact W]]; subst E; reflexivity. }
eapply (knode_mmap_rw src0segs regs2 _ mem2 (seg_rom src0segs) md A (n + IB + UNIT)).
- exact Hh. - exact Hlz.
- rewrite (Hregs2 17%bv). vm_compute. reflexivity.
- rewrite (Hregs2 11%bv). eval_sr_get. cbn [sv_denot]. subst E. cbn [ew E_entry E_mi]. rewrite Hn'. unfold IB, UNIT. f_equal. lia.
- unfold IB, UNIT. lia.
- rewrite (Hregs2 12%bv). vm_compute. reflexivity.
- rewrite (Hregs2 13%bv). vm_compute. reflexivity.
- rewrite (Hregs2 14%bv). eval_sr_get. cbn [sv_denot]. apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs2 15%bv). vm_compute. reflexivity.
-
intros e He. destruct He as [<- | []].
match goal with |- mreal _ _ ?t _ => change t with (@IRet astate (option sptr * astate) (None, A)) end.
apply mreal_IRet.
assert (Ee : errno_ret ENOMEM = Z_to_bv 64 (2 ^ 64 - 12)) by (apply bv_eq; vm_compute; reflexivity). rewrite Ee.
pose proof (st_ok_refused regs (st_seq A) (st_mmap_counter A) (useq_of A) (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0)
regs2 mem2 Hregs2 Hmem2 HG2) as HS.
change (E_mi regs (st_seq A) (st_mmap_counter A) (useq_of A) (Z_to_bv 64 0) (Z_to_bv 64 0) (fun _ => Z_to_bv 64 0)) with E in HS.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_refused ss_ref_end); [exact Hh | exact Hlz | exact HS | apply run_refused |].
clear HS. intros ms4 HS HF4. cbn [ms_mem] in HF4.
eapply (SR_final_ret E ss_ref_end ms4 md); [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | subst E; exact Hret | exact Hh | exact Hlz |].
subst E. cbn [ew E_entry E_mi]. intros _.
apply (leaf_unchanged L A regs mem md n (ms_regs ms4) (ms_mem ms4) PRE).
+ intros x Hx Hns. rewrite (HF4 (Z_to_bv 64 x)); [apply FR2; assumption|].
rewrite u64_of_Z by exact Hx. intros W. apply Hns. eapply (in_wrange_scratch _ regs _ x sk_refused); [| exact W]. reflexivity.
+ intros x Hsx. eapply (scratch_writable_sym _ _ _ _ _ _ _ ss_ref_end); [apply (proj2 ref_end_checks) | exact HS |].
unfold scratch, spZ, ALLOC_STACK in Hsx. rewrite B_errno in Hsx. exact Hsx.
+ eapply (regs_preserved_sym _ _ _ _ _ _ _ ss_ref_end); [apply (proj1 ref_end_checks) | exact HS | exact Htp].
+ pose proof (st_ok_reg src0segs _ _ _ 10 HS) as R. rewrite R. vm_compute. reflexivity.
-
intros a GRa.
assert (GR : grant_ok (Z_to_bv 64 0) md a (dlen n) = true).
{ revert GRa. rewrite (Hregs2 10%bv). eval_sr_get. cbn [sv_denot]. unfold dlen, dm_len. intros G. exact G. }
match goal with |- mreal _ _ ?t _ => change t with (dm_rest n A) end.
exact (granted_branch L A regs mem md n regs2 mem2 a PRE Hn Hrange Hregs2 Hmem2 HG2 FR2 GR).
-
intros Hmg. rewrite (Hregs2 10%bv). eval_sr_get. cbn [sv_denot].
apply (direct_grant_exists L A mem md (n + IB + UNIT) MX Hmg). unfold IB, UNIT. lia.
Qed.
End h.
Theorem src0_malloc_realizes :
alloc_meta_hyp B -> malloc_small_hyp B -> malloc_realizes B (MRx B).
Proof.
intros AMH SMALL L A regs mem md n PRE Hn Hr.
destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs | Hd].
- exact (SMALL L A regs mem md n PRE Hn ltac:(lia)).
- rewrite B_segs, B_malloc. exact (malloc_direct_mreal AMH L A regs mem md n PRE Hn ltac:(lia)).
Qed.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
