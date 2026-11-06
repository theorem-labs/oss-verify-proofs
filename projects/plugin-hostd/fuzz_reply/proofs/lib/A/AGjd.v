(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjd.v (a working branch 30a1993588f, c5 + memnorm; file sha256 e6897ec078e0) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 4 image addresses moved by code-verified function pairs (5 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; no other numeral changed. *)
(* The machine facts of the hit-k seed of the frame-generic Allocate walk (requests of 0..48 bytes), read from the
   view [AGif0cgif.hview] (no allocator model): the k twin of AGiz, over the k hub AGj6 (RZ = 16, NPv = max n 1).

   Section v: the view lemmas [vw_*] (the released YFiy scripts with each ARm read replaced by a field of the view).
   Every [vw_*] lemma takes the same arguments, in this order (Proof using All):
     {fx} {rc} B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class.
   Section h: REG0K_head_ok : the seed's first regions (the stack object, the scratch window, the empty slot and
   firstn 37 TAIL0KG: the image's literal cells, the instance's fields, the thread and context objects' fixed words)
   hold at Allocate's entry.  Its premises are the frame and the view's fields that do not read the cached chunk,
   each a separate premise named as the field of the proposed miss view (mv_ly, mv_img, ...), so that the k miss seed
   reuses it.
   Section r: REG0K_r39_ok : the thread's unwinding byte (nth 39 of AGi4.RG0K), from the layout and that byte.
   Section e: the walk header (AGj6's section header, with the allocator instance [inst] at atom aINST and the view
   in place of the model) and REG0K_ok : the regions of the k seed AGhy.REG0KG hold at Allocate's entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
(* AGif0cgif.hview reads the cached chunk at AGis.Kv / SKv / Pv / PVv; the k hub's AGj6 constants have the same bodies. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGis.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AFhy AGhy AFi1 AGj6 AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *; lia ].
Lemma vw_val_mem_mod8 : forall m a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x H k Hk. rewrite (H k Hk). do 2 f_equal. rewrite <- (le_byte_eq x), <- (le_byte_eq (x mod 2 ^ 64)). unfold YG0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by zlia. reflexivity.
Qed.
(* The image's constant cells, from the constant-cell field of a view (AGiz.vw_cell_lit / vw_cell_sym). *)
Lemma const_lit : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte), TfibSyms B ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) ->
forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) a w x.
Proof.
intros B W ly mem0 TS HCONST a w x E. apply (cell_holds_val_mem B ly (w_H W) mem0 (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) HCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma const_sym : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte), TfibSyms B ->
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly) ->
forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (aeval B ly e) w (aeval B ly e').
Proof.
intros B W ly mem0 TS HCONST e w e' E. apply (cell_holds_val_mem B ly (w_H W) mem0 e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly)) HCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
(* The chunks of a region (AGiz.chunk_lit / chunk_lit_at / chunk_atom over any environment and memory). *)
Lemma chunk_lit_g : forall (E : env) (m : word -> option byte) a (nn : BinNums.N) x,
val_mem tfibsegs m a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E m 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros E m a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_at_g : forall (E : env) (m : word -> option byte) base a (nn : BinNums.N) x,
val_mem tfibsegs m (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros E m base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atom_g : forall (E : env) (m : word -> option byte) base a (nn : BinNums.N) k d x, ew E k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof.
intros E m base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
(* The hub's layout lemmas (AGj6.high_facts / off_T / off_C) read only the layout; their sections also take the
   cached-chunk index v and the trace, given here as 0 and [0]. *)
Lemma hf_v0 : 0 <= 0 /\ 16 * 0 + 2 ^ 16 <= 2 ^ 32.
Proof. lia. Qed.
Lemma hf_tr0 : (1 <= length [0%Z] <= 30)%nat.
Proof. cbn. lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The view lemmas.                                                                                                 *)
Section v.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (inst : Z) (mem0 : word -> option byte).
Variables (n cl cnt v : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HV : hview B W ly inst mem0 cl cnt v.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hcl_class : cl = chunk_class n.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation case0_sizes := (@AGj6.case0_sizes n Nrange).
Local Abbreviation K0_facts := (@AGj6.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
Ltac vw := pose proof HV as [HLY HIMG HTSD HCNT HVV HCONST HINST HCACHE HUNW HJUNK HCHUNK HSHADOW];
change (AGis.Kv ly cl v) with Kv in HCHUNK; change (AGis.SKv ly cl v) with SKv in HSHADOW;
change (AGis.PVv ly cl cnt) with PVv in HCACHE; change (AGis.Pv ly cl) with Pv in HCACHE.
Lemma vw_cl_range : 1 <= cl <= 30.
Proof using All.
pose proof case0_sizes as (_ & _ & _ & _ & FP & _).
pose proof (primary_geometry n ltac:(zlia) FP) as (G & _). rewrite <- Hcl_class in G. exact G.
Qed.
Lemma vw_cls_geom :
0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16 /\
RZ + NPv <= class_size cl /\ RZ + R8v <= class_size cl.
Proof using All.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
pose proof case0_sizes as (_ & RS & R8 & NP & FP & NS & RQ).
pose proof (primary_geometry n ltac:(zlia) FP) as (G1 & G2 & G3 & G4 & G5). rewrite <- Hcl_class in *.
pose proof (class_ok cl ltac:(zlia)) as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite RS, RQ, NS in G2. repeat split; try zlia.
Qed.
Lemma vw_Hcl : 1 <= cl <= 31.
Proof using All. pose proof vw_cl_range. zlia. Qed.
Lemma vw_Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof using All. vw. destruct HVV as (V0 & V2 & V3). pose proof vw_cls_geom as (K1 & _). zlia. Qed.
Lemma vw_Hv2 : v mod 2 = 0.
Proof using All. vw. exact (proj1 (proj2 HVV)). Qed.
Lemma vw_Hcnt : 1 <= cnt <= 16.
Proof using All. vw. exact HCNT. Qed.
Lemma vw_Hcl_def : cl = class_id (R8v + RZ).
Proof using All. pose proof case0_sizes as (_ & _ & _ & _ & _ & NS & _). rewrite Hcl_class. unfold chunk_class. rewrite NS. reflexivity. Qed.
(* The k classes: needed_size n = R8v + 16 is in 24..64, so the class is 1 or 2 (FK's aCL fact). *)
Lemma vw_cl_k0 : 1 <= cl <= 2.
Proof using All.
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
assert (E : class_id (R8v + RZ) = (R8v + RZ + 31) / 32).
{ unfold class_id. destruct (Z.leb_spec (R8v + RZ) 512); [reflexivity | exfalso; zlia]. }
rewrite vw_Hcl_def, E.
pose proof (Z.div_le_lower_bound (R8v + RZ + 31) 32 1 ltac:(zlia) ltac:(zlia)).
pose proof (Z.div_lt_upper_bound (R8v + RZ + 31) 32 3 ltac:(zlia) ltac:(zlia)). zlia.
Qed.
Lemma vw_Kv_geom : kHighMemBeg <= Kv /\ Kv + class_size cl <= ASAN_CEIL /\ Kv mod 16 = 0 /\
ly_prim ly <= Kv /\ Kv + class_size cl <= ly_prim ly + kPrimResvSize.
Proof using All.
vw. destruct HVV as (V0 & V2 & V3). pose proof vw_cl_range as CR. pose proof vw_cls_geom as (K1 & _ & K3 & _). unfold kMaxSize in K3.
pose proof (region_in_prim ly cl HLY ltac:(zlia)) as (R1 & R2 & R3 & R4 & R5).
assert (KB : Kv = region_base ly cl + 16 * v) by (unfold AGj6.Kv, region_base; rewrite region_off_eq by zlia; zlia).
assert (M16 : (region_base ly cl + 16 * v) mod 16 = 0).
{ apply Z.mod_divide in R3 as [q Hq]; [|zlia]. apply Z.mod_divide; [zlia|]. exists (q * 4096 + v). zlia. }
rewrite KB. split; [zlia|]. split; [zlia|]. split; [exact M16|]. split; zlia.
Qed.
Lemma vw_Kv32 : Kv mod 32 = 0.
Proof using All.
vw. destruct HVV as (V0 & V2 & V3). pose proof (lo_space_al ly HLY) as SAL.
apply Z.mod_divide in SAL as [q Hq]; [|zlia]. apply Z.mod_divide in V2 as [w Hw]; [|zlia].
unfold AGj6.Kv. rewrite Hq, Hw. apply Z.mod_divide; [zlia|]. exists (q * 2048 + cl * 2 ^ 27 + w). zlia.
Qed.
Lemma vw_KPRES : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Proof using All. vw. intros a Ha. pose proof vw_cls_geom as (_ & _ & _ & _ & _ & K6). apply HCHUNK. zlia. Qed.
Lemma vw_SKPRES : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Proof using All.
vw. intros a Ha. pose proof vw_cls_geom as (K1 & _ & _ & _ & _ & K6). pose proof RZ_num as (RZr & _).
pose proof (Z.div_le_mono (RZ + R8v) (class_size cl) 8 ltac:(zlia) K6) as DM.
exact (proj1 (HSHADOW a ltac:(zlia))).
Qed.
(* The partial shadow byte of an odd request lies in the chunk's poisoned shadow (k: NPv = max n 1, so n = 0 is odd). *)
Lemma vw_PB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Proof using All.
vw. intros E8. pose proof vw_cls_geom as (K1 & _ & _ & _ & _ & K6).
pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
pose proof K0_facts as (_ & _ & _ & _ & _ & _ & KR8 & _ & _ & _ & KN8 & _ & _ & _ & _ & KN8D & _).
pose proof vw_Kv_geom as (V1 & V2 & V3 & _).
assert (N8lt : N8D < NPv).
{ rewrite KN8D. pose proof (Z.div_mod NPv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound NPv 8 ltac:(zlia)). zlia. }
apply Z.mod_divide in KR8 as [ra Hra]; [|zlia]. apply Z.mod_divide in KN8 as [rb Hrb]; [|zlia].
apply Z.mod_divide in V3 as [q Hq]; [|zlia].
assert (EK8 : Kv / 8 = 2 * q) by (rewrite Hq; replace (q * 16) with ((2 * q) * 8) by zlia; apply Z.div_mul; zlia).
assert (EP8 : (Kv + RZ + N8D) / 8 = 2 * q + 2 + rb).
{ rewrite Hq, Hrb, RZr. replace (q * 16 + 16 + rb * 8) with ((2 * q + 2 + rb) * 8) by zlia. apply Z.div_mul. zlia. }
assert (CS8 : rb + 3 <= class_size cl / 8) by (apply Z.div_le_lower_bound; zlia).
assert (RNG : SKv <= PBv < SKv + class_size cl / 8).
{ unfold AGj6.PBv, AGj6.SKv. rewrite EP8, EK8. zlia. }
exact (proj2 (HSHADOW PBv RNG)).
Qed.
Lemma vw_junk_word : forall a, ly_T ly + t_cache_stats <= a -> a + 8 <= ly_T ly + t_unwinding ->
exists w, val_mem tfibsegs (mrestrict (w_H W) mem0) a 8 w.
Proof using All.
vw. intros a H1 H2.
assert (BY : forall k, (k < 8)%nat -> exists b, mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat k) = Some b).
{ intros k Hk. apply apresent_mbyte. apply HJUNK. zlia. }
destruct (BY 0%nat ltac:(zlia)) as [b0 B0]. destruct (BY 1%nat ltac:(zlia)) as [b1 B1]. destruct (BY 2%nat ltac:(zlia)) as [b2 B2]. destruct (BY 3%nat ltac:(zlia)) as [b3 B3].
destruct (BY 4%nat ltac:(zlia)) as [b4 B4]. destruct (BY 5%nat ltac:(zlia)) as [b5 B5]. destruct (BY 6%nat ltac:(zlia)) as [b6 B6]. destruct (BY 7%nat ltac:(zlia)) as [b7 B7].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5. pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
change (bv_modulus 8) with 256 in R0, R1, R2, R3, R4, R5, R6, R7.
exists (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))).
assert (LB : forall (z q b : Z) (k : nat) r, (k < 8)%nat -> 0 <= b < 256 -> 0 <= q -> 0 <= r < 2 ^ (8 * Z.of_nat k) ->
z = 2 ^ (8 * Z.of_nat k) * (b + 256 * q) + r -> z < 2 ^ 64 -> le_byte z 8 k = b).
{ clear. intros z q b k r Hk Hb Hq Hr Hz Hz64. unfold le_byte. rewrite Z.shiftr_div_pow2 by zlia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); zlia).
rewrite <- (Z.div_unique z (2 ^ (8 * Z.of_nat k)) (b + 256 * q) r ltac:(left; exact Hr) Hz).
symmetry. apply (Z.mod_unique _ 256 q b); zlia. }
match goal with |- val_mem _ _ _ _ ?w => set (WW := w) end.
assert (GOAL : forall (bk : byte) kk, mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some bk -> YG0f.le_byte WW 8 kk = bv_unsigned bk ->
mbyte tfibsegs (mrestrict (w_H W) mem0) (a + Z.of_nat kk) = Some (Z_to_bv 8 (YO0f.le_byte WW 8 kk))).
{ intros bk kk Hm Hl. rewrite Hm, <- le_byte_eq, Hl, Z_to_bv_bv_unsigned. reflexivity. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [..|zlia];
[ apply (GOAL b0 0%nat B0) | apply (GOAL b1 1%nat B1) | apply (GOAL b2 2%nat B2) | apply (GOAL b3 3%nat B3)
| apply (GOAL b4 4%nat B4) | apply (GOAL b5 5%nat B5) | apply (GOAL b6 6%nat B6) | apply (GOAL b7 7%nat B7) ]; subst WW.
- apply (LB _ ((bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))))) _ 0%nat (0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | change (2 ^ (8 * Z.of_nat 0)) with 1; zlia | zlia].
- apply (LB _ ((bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))) _ 1%nat (bv_unsigned b0)); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | change (2 ^ (8 * Z.of_nat 1)) with 256; zlia | zlia].
- apply (LB _ ((bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))))) _ 2%nat ((bv_unsigned b0 + 256 * bv_unsigned b1))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | change (2 ^ (8 * Z.of_nat 2)) with 65536; zlia | zlia].
- apply (LB _ ((bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))) _ 3%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; zlia | zlia].
- apply (LB _ ((bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7))) _ 4%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | change (2 ^ (8 * Z.of_nat 4)) with 4294967296; zlia | zlia].
- apply (LB _ ((bv_unsigned b6 + 256 * bv_unsigned b7)) _ 5%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * bv_unsigned b4)))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | change (2 ^ (8 * Z.of_nat 5)) with 1099511627776; zlia | zlia].
- apply (LB _ (bv_unsigned b7) _ 6%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * bv_unsigned b5))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | change (2 ^ (8 * Z.of_nat 6)) with 281474976710656; zlia | zlia].
- apply (LB _ (0) _ 7%nat ((bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * bv_unsigned b6)))))))); [zlia | zlia | zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | change (2 ^ (8 * Z.of_nat 7)) with 72057594037927936; zlia | zlia].
Qed.
Lemma vw_junk_byte : forall a, Kv <= a < Kv + RZ + R8v -> exists b, 0 <= b <= 255 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) a 1 b.
Proof using All.
intros a Ha. destruct (vw_KPRES a Ha) as [Hh [b Hb]]. exists (bv_unsigned b).
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. split; [zlia|].
intros k Hk. destruct k; [|zlia]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh, Hb. f_equal.
rewrite <- le_byte_eq. unfold YG0f.le_byte. rewrite Z.shiftr_0_r. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small (bv_unsigned b)) by zlia. rewrite Z.mod_small by zlia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma vw_junk_values : exists j0 j1 j2 j3 j4 jb,
val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2784) 8 j0 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2800) 8 j1 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2808) 8 j2 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + 2816) 8 j3 /\
val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4 /\ 0 <= jb <= 255 /\ val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Proof using All.
pose proof vw_cl_range as CR. pose proof RZ_num as (RZr & RZ8 & Nlo & NPr & R8r & NPR8 & N8r & NPN8 & FILN).
destruct (vw_junk_word (ly_T ly + 2784)) as [x0 Q0]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (vw_junk_word (ly_T ly + 2800)) as [x1 Q1]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (vw_junk_word (ly_T ly + 2808)) as [x2 Q2]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (vw_junk_word (ly_T ly + 2816)) as [x3 Q3]; [unfold t_cache_stats; zlia | unfold t_unwinding; zlia |].
destruct (vw_junk_word SSLOTv) as [x4 Q4]; [unfold AGj6.SSLOTv, t_stats, t_cache_stats; zlia | unfold AGj6.SSLOTv, t_stats, t_unwinding; zlia |].
destruct (vw_junk_byte (Kv + RZ - 15)) as (xb & Rb & Hb); [zlia|].
exists x0, x1, x2, x3, x4, xb. repeat split; try assumption; zlia.
Qed.
Lemma vw_cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) a w x.
Proof using All. vw. exact (const_lit B W ly mem0 TS HCONST). Qed.
Lemma vw_cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict (w_H W) mem0) (aeval B ly e) w (aeval B ly e').
Proof using All. vw. exact (const_sym B W ly mem0 TS HCONST). Qed.
Lemma vw_cache_vals : val_mem tfibsegs (mrestrict (w_H W) mem0) Pv 4 cnt /\
val_mem tfibsegs (mrestrict (w_H W) mem0) (Pv + 8) 8 (class_size cl) /\ val_mem tfibsegs (mrestrict (w_H W) mem0) PVv 4 v.
Proof using All. vw. exact HCACHE. Qed.
Lemma vw_unwinding_val : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + t_unwinding) 1 0.
Proof using All. vw. exact HUNW. Qed.
Lemma vw_sk_val : val_mem tfibsegs (mrestrict (w_H W) mem0) SKv 1 250.
Proof using All.
vw. pose proof vw_cls_geom as (K1 & K2 & _).
assert (CS : 32 <= class_size cl) by (apply Z.mod_divide in K2 as [q Hq]; [zlia | zlia]).
pose proof (Z.div_le_mono 32 (class_size cl) 8 ltac:(zlia) CS) as D. change (32 / 8) with 4 in D.
exact (proj2 (HSHADOW SKv ltac:(zlia))).
Qed.
End v.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed's first regions, from the frame and the view's fields that do not read the cached chunk.                *)
Section h.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AGj6.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AGj6.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AGj6.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AGj6.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AGj6.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E11 := (@AGj6.E11 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Hypothesis mv_ly : layout_ok ly.
Hypothesis mv_img : img_cover ly.
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Variables (B : asyms) (inst : Z).
Hypothesis TS : TfibSyms B.
Hypothesis mv_tsd : ly_tsd ly = TFIB_TSD.
Hypothesis mv_const : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem0)) (as_const B ly).
Hypothesis mv_inst : val_mem tfibsegs (mrestrict (w_H W) mem0) (inst + 0x20) 8 (ly_space ly) /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (inst + 0xe20) 8 0x10000000000 /\
  val_mem tfibsegs (mrestrict (w_H W) mem0) (inst + 0xe28) 8 0x108000010.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis HIO : inst_ok inst.
Let m0 := mrestrict (w_H W) mem0.
Hypothesis PSO : val_mem tfibsegs m0 SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs m0 (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n tr 0 hf_v0 mv_ly mv_img Htrlen (fun _ _ => True)).
Local Abbreviation off_T := (@AGj6.off_T _ ly regs0 mem0 n tr 0 hf_v0 mv_ly mv_img Htrlen (fun _ _ => True)).
Local Abbreviation off_C := (@AGj6.off_C _ ly regs0 mem0 n tr 0 hf_v0 mv_ly mv_img Htrlen (fun _ _ => True)).
Local Abbreviation off_NB := (@AGj6.off_NB _ ly mv_ly mv_img).
Local Abbreviation off_SB := (@AGj6.off_SB _ ly mv_ly mv_img).
Local Abbreviation cell_lit := (const_lit B W ly mem0 TS mv_const).
Local Abbreviation cell_sym := (const_sym B W ly mem0 TS mv_const).
Local Abbreviation chunk_lit := (chunk_lit_g E0 m0).
Local Abbreviation chunk_lit_at := (chunk_lit_at_g E0 m0).
Local Abbreviation chunk_atom := (chunk_atom_g E0 m0).
Ltac h_off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Ltac h_reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac h_lit_region :=
h_reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
Lemma REG0K_head_ok : Forall (region_ok tfibsegs E0 m0) (R_soG :: R_scrG :: R_slotG :: firstn 37 TAIL0KG).
Proof using All.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9).
pose proof (lo_top ly mv_ly) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
destruct HIO as (IO1 & IO2 & IO3).
assert (EI : bv_unsigned (ew E0 11) = inst) by (rewrite E11, Hi11; unfold w64; apply unsigned_lit_small; zlia).
assert (ESO : bv_unsigned (ew E0 13) = SOv) by (rewrite (Er 13 13%bv eq_refl); reflexivity).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, T2, T4, T7.
unfold TAIL0KG, TAIL0G. cbn [firstn app].
unfold R_soG, R_scrG, R_slotG, iatom8, ilits8, lit1, lit4, lit8, lits8, atom8, CTZ_TABLE.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aINST, aSO, aBP, aLEN.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{   h_reg_intro. rewrite ESO. pose proof (u64_range (getr regs0 13)) as U13.
split; [unfold SOv; zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom SOv 0 8 12%nat 0 BPv);
[ rewrite Z.sub_0_r, (Er 12 12%bv eq_refl); unfold w64, BPv; symmetry; apply Z_to_bv_bv_unsigned
| pose proof (u64_range (getr regs0 12)); unfold BPv; zlia | rewrite Z.add_0_r; exact PSO
| unfold BPv; pose proof (u64_range (getr regs0 12)); change (8 * Z.of_N 8) with 64; zlia | cbn; zlia ].
- apply (chunk_atom SOv 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | zlia | exact PLEN | change (8 * Z.of_N 8) with 64; zlia | cbn; zlia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- AFSTACK)); [rewrite E2; reflexivity | unfold AFSTACK; zlia | zlia |].
intros a Ha. apply apresent_writable_off; [h_off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, AFSTACK in *; zlia) | apply Hpres0; exact Ha]. }
(* the empty slot *)
apply Forall_cons.
{   h_reg_intro. rewrite E2. pose proof (u64_range (getr regs0 2)). split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia | apply Forall_nil]. }
do 8 (apply Forall_cons; [h_lit_region|]).
(* the instance's primary.space field *)
apply Forall_cons. {   h_reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom inst 32 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | exact (proj1 mv_inst) | unfold SB; cbn; zlia | cbn; zlia]. }
(* the instance's words at +0xe20 *)
apply Forall_cons. {   h_reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
destruct mv_inst as (_ & HI2 & HI3).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (apply chunk_lit_at; [assumption | cbn; zlia | cbn; zlia]). }
do 13 (apply Forall_cons; [h_lit_region|]).
apply Forall_cons. {   h_reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 47%nat 0 SHBv); [reflexivity | unfold AGj6.SHBv; zlia | | unfold AGj6.SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 7 (apply Forall_cons; [h_lit_region|]).
apply Forall_cons. {   h_reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| cbn; zlia | cbn; zlia]. pose proof (cell_lit 0x5d9480 8 0 ltac:(vm_compute; reflexivity)) as H8.
intros k Hk. unfold m0. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [h_lit_region|].
apply Forall_cons. {   h_reg_intro. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace (6132848 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite mv_tsd; unfold TFIB_TSD; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   h_reg_intro. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6268952 with (aeval B ly (ATsd 0)) by (cbn; rewrite mv_tsd; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   h_reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   h_reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; zlia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; zlia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; zlia | unfold kStackSpan; zlia | | unfold kStackSpan; cbn; zlia | cbn; zlia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; zlia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; zlia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; zlia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_nil.
Qed.
End h.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The thread's unwinding byte (TAIL0KG's region 38 = nth 39 of AGi4.RG0K = the miss seed's kept unwinding region).  *)
Section r.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Hypothesis mv_ly : layout_ok ly.
Hypothesis mv_img : img_cover ly.
Hypothesis mv_unw : val_mem tfibsegs (mrestrict (w_H W) mem0) (ly_T ly + t_unwinding) 1 0.
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n [0] 0 hf_v0 mv_ly mv_img hf_tr0 (fun _ _ => True)).
Local Abbreviation off_T := (@AGj6.off_T _ ly regs0 mem0 n [0] 0 hf_v0 mv_ly mv_img hf_tr0 (fun _ _ => True)).
Local Abbreviation chunk_lit_at := (chunk_lit_at_g E0 (mrestrict (w_H W) mem0)).
Lemma REG0K_r39_ok : region_ok tfibsegs E0 (mrestrict (w_H W) mem0)
  (YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YP09.mkChunk t_unwinding (CVal 1 (SLit 0))]).
Proof using All.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9).
pose proof (lo_top ly mv_ly) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, T2, T4, T7.
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold aT.
rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho.
  apply apresent_writable_off; [first [ apply off_img_high; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
                                      | apply off_T; unfold kThreadObjSize; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia ] |].
  replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
  pose proof mv_unw as U.
  eapply mbyte_off_apresent; [first [ apply off_img_high; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia
                                    | apply off_T; unfold kThreadObjSize; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia ] |].
  unfold t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). exact (U 0%nat ltac:(zlia)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact mv_unw.
Qed.
End r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk header (AGj6's section header) with the view, and the seed's regions.                                   *)
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation Uv := (@AGj6.Uv ly cl v).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AGj6.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AGj6.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AGj6.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AGj6.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AGj6.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E11 := (@AGj6.E11 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AGj6.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AGj6.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AGj6.EaSK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AGj6.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AGj6.EaPV ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
(* The stack object and the trace buffer lie in the caller's frame, above Allocate's entry sp. *)
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x177f88.
(* can_fill (atom 15) is 0 or 1. *)
Hypothesis Hcf : getr regs0 15 = w64 0 \/ getr regs0 15 = w64 1.
Variable DPOST : Z -> (word -> option byte) -> Prop.
Hypothesis Nrange : 0 <= n <= 48.
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Variables (B : asyms) (inst : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HV : hview B W ly inst mem0 cl cnt v.
Hypothesis Hi11 : getr regs0 11 = w64 inst.
Hypothesis HIO : inst_ok inst.
Let m0 := mrestrict (w_H W) mem0.
Hypothesis PSO : val_mem tfibsegs m0 SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs m0 (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Local Abbreviation Kv_range := (@AGj6.Kv_range ly regs0 mem0 n tr cl v Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_T := (@AGj6.off_T _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGj6.off_C _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGj6.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGj6.off_SB _ ly LY IMG).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
Local Abbreviation derived_ranges := (@AGj6.derived_ranges _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation vcls := (vw_cls_geom B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vKgeom := (vw_Kv_geom B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vKPRES := (vw_KPRES B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vsk_val := (vw_sk_val B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation vcache := (vw_cache_vals B W ly inst mem0 n cl cnt v TS HV Nrange Hcl_class).
Local Abbreviation chunk_lit_at := (chunk_lit_at_g E0 m0).
Local Abbreviation chunk_atom := (chunk_atom_g E0 m0).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Lemma REG0K_ok : Forall (region_ok tfibsegs E0 m0) REG0KG.
Proof.
pose proof HV as [HLY HIMG HTSD HCNT HVV HCONST HINST HCACHE HUNW HJUNK HCHUNK HSHADOW].
(* the stack object, the scratch window, the empty slot and the image / instance / thread / context cells *)
assert (HD : Forall (region_ok tfibsegs E0 m0) (R_soG :: R_scrG :: R_slotG :: firstn 37 TAIL0KG)) by (eapply REG0K_head_ok; eassumption).
(* the unwinding byte *)
assert (R39 : region_ok tfibsegs E0 m0
  (YP09.mkRegion (Some aT) t_unwinding (t_unwinding + 1) t_unwinding (t_unwinding + 1) [YP09.mkChunk t_unwinding (CVal 1 (SLit 0))]))
  by (eapply REG0K_r39_ok; eassumption).
unfold REG0KG. rewrite <- (firstn_skipn 37 TAIL0KG).
change (Forall (region_ok tfibsegs E0 m0) ((R_soG :: R_scrG :: R_slotG :: firstn 37 TAIL0KG) ++ skipn 37 TAIL0KG)).
apply Forall_app. split; [exact HD|]. clear HD.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hf9). pose proof derived_ranges as DR. pose proof Kv_range as HKR.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
pose proof vcache as (CV1 & CV2 & CV3). rewrite <- Hcsz_def in CV2.
pose proof vKgeom as (V1 & V2 & V3 & V4 & V5). pose proof vcls as (K1 & K2 & K3 & K4 & K5 & K6).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, DR, HKR, T2, T4, T7.
unfold TAIL0KG, TAIL0G. cbn [skipn firstn app].
apply Forall_cons. {   reg_intro. unfold aT, aJ0. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |].
apply HJUNK. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 37%nat 0 (j0 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia | apply vw_val_mem_mod8; exact Hj0 | cbn; pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia | cbn; zlia]. }
apply Forall_cons; [exact R39|].
apply Forall_cons. {   reg_intro. unfold aT, aJ1, aJ2, aJ3. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |].
apply HJUNK. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 8 49%nat 0 (j1 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia | apply vw_val_mem_mod8; exact Hj1 | cbn; pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 50%nat 0 (j2 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia | apply vw_val_mem_mod8; exact Hj2 | cbn; pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 51%nat 0 (j3 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia | apply vw_val_mem_mod8; exact Hj3 | cbn; pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. unfold aSSLOT, aJ4. rewrite EaSSLOT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |].
apply HJUNK. unfold AGj6.SSLOTv, T, t_cache_stats, t_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 53%nat 0 (j4 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j4 (2 ^ 64)); zlia | apply vw_val_mem_mod8; rewrite Z.add_0_r; exact Hj4 | cbn; pose proof (Z.mod_pos_bound j4 (2 ^ 64)); zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. unfold aP, aCNT. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. destruct (Z.eq_dec o 0) as [->|]; [|destruct (Z.eq_dec o 1) as [->|]; [|destruct (Z.eq_dec o 2) as [->|]; [|replace o with 3 by zlia]]];
[ eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 0 = Pv + 0); exact (CV1 0%nat ltac:(zlia))]
| eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 1 = Pv + 1); exact (CV1 1%nat ltac:(zlia))]
| eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 2 = Pv + 2); exact (CV1 2%nat ltac:(zlia))]
| eapply mbyte_off_apresent; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) | rewrite <- (eq_refl : Pv + Z.of_nat 3 = Pv + 3); exact (CV1 3%nat ltac:(zlia))] ]. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 4 41%nat 0 cnt); [rewrite Z.sub_0_r; reflexivity | zlia | rewrite Z.add_0_r; exact CV1 | cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. unfold aP, aCSZ. rewrite EaP. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 43%nat 0 (csz mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound csz (2 ^ 64)); zlia | apply vw_val_mem_mod8; exact CV2 | cbn; pose proof (Z.mod_pos_bound csz (2 ^ 64)); zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. unfold aPV, aV. rewrite EaPV. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 4 42%nat 0 v); [rewrite Z.sub_0_r; reflexivity | zlia | rewrite Z.add_0_r; exact CV3 | cbn; zlia | cbn; zlia]. }
(* the chunk's header line: the k seed keeps its byte 1 (YFi1.REG0K) *)
apply Forall_cons. {   reg_intro. unfold aK, aJB. rewrite EaK. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply vKPRES. zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 1 46%nat 0 jb); [rewrite Z.sub_0_r; reflexivity | zlia | | cbn; zlia | cbn; zlia].
replace (Kv + 1) with (Kv + RZ - 15) by zlia. exact Hjb_def. }
apply Forall_cons; [|apply Forall_nil]. {   reg_intro. unfold aSK. rewrite EaSK. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. rewrite Z.add_0_r. exact vsk_val. }
Qed.
End e.
End d.
About REG0K_head_ok.
About REG0K_r39_ok.
About REG0K_ok.
About vw_PB250.
About vw_junk_values.
About vw_KPRES.
