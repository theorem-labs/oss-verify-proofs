(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0f.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition SHADOW_OFF : Z := 0x7fff8000.
Definition kHighMemBeg : Z := 0x10007fff8000.
Definition kHighMemEnd : Z := 0x800000000000.
Definition ASAN_CEIL {rc : YM05.RunCeil} : Z := alloc_ceiling.
Lemma ASAN_CEIL_range {rc : YM05.RunCeil} : 0x7fff7f800000 <= ASAN_CEIL <= 0x7fffff800000 /\ ASAN_CEIL mod 4096 = 0.
Proof. exact alloc_ceiling_val. Qed.
Definition kLowMemEnd : Z := 0x7fff8000.
Definition kImgEnd : Z := 0x677000.
Definition kImgLo : Z := 0x10000.
Definition kLowShadowBeg : Z := 0x7fff7000.
Definition kLowShadowEnd : Z := 0x8fff7000.
Definition kHighShadowBeg : Z := 0x2008fff7000.
Definition kHighShadowEnd : Z := 0x10007fff8000.
Definition kPrimResvSize : Z := 0x2000011000.
Definition kSpaceSize : Z := 2 ^ 37.
Definition kRegionInfoOff : Z := 2 ^ 37.
Definition kPtrArrayResv : Z := 0x800000.
Definition kThreadObjSize : Z := 4096.
Definition kFakeStackSize : Z := 0xb09000.
Definition kFakeFlagsOff : Z := 4096.
Definition kFakeFramesOff : Z := 4096 + 32768.
Definition kNodesBlockSize : Z := 0x100000.
Definition kStoreBlockSize : Z := 0x800000.
Definition kCtxMapSize : Z := 65536.
Definition kStackSpan : Z := 2 ^ 23.
Definition fs_flags_off (cid : Z) : Z := Z.shiftl (Z.shiftl (Z.shiftr 1023 (10 - cid)) (10 - cid)) (kStackSizeLog - 15).
Definition fs_flag_off (cid pos : Z) : Z := kFakeFlagsOff + fs_flags_off cid + pos.
Definition fs_frame_off (cid pos : Z) : Z := kFakeFramesOff + cid * Z.shiftl 1 kStackSizeLog + pos * fs_frame_bytes cid.
Example fs_flags_off_ok : map fs_flags_off [0; 1; 2; 10] = [0; 16384; 24576; 32736] /\
map (fun c => fs_frame_off c 1) [1; 2] = [36864 + 1048576 + 128; 36864 + 2097152 + 256].
Proof. vm_compute. split; reflexivity. Qed.
Record alayout := ALayout {
ly_prim : Z;
ly_space : Z;
ly_Q : Z;
ly_T : Z;
ly_C : Z;
ly_F : Z;
ly_NB : Z;
ly_SB : Z;
ly_top : Z;
ly_stk_lo : Z;
ly_stk_hi : Z;
ly_tsd : Z;
ly_tr0 : list Z;
ly_extra : list (Z * Z);
ly_D : Z;
ly_vis0 : list (Z * Z);
ly_img : Z * Z;
ly_sec : nat -> Z
}.
Definition ly_bot (ly : alayout) : Z := ly_top ly - kStackSpan.
Definition ly_rinfo (ly : alayout) : Z := ly_space ly + kRegionInfoOff.
Definition layout_le (nsecs : nat) (ly ly' : alayout) : Prop :=
ly_prim ly' = ly_prim ly /\ ly_space ly' = ly_space ly /\ ly_Q ly' = ly_Q ly /\ ly_T ly' = ly_T ly /\
ly_C ly' = ly_C ly /\ ly_F ly' = ly_F ly /\ ly_NB ly' = ly_NB ly /\ ly_SB ly' = ly_SB ly /\
ly_top ly' = ly_top ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\ ly_tsd ly' = ly_tsd ly /\
ly_tr0 ly' = ly_tr0 ly /\ ly_extra ly' = ly_extra ly /\ ly_D ly' = ly_D ly /\ ly_img ly' = ly_img ly /\
forall r, (r < nsecs)%nat -> ly_sec ly' r = ly_sec ly r.
Lemma layout_le_refl : forall n ly, layout_le n ly ly.
Proof. intros n ly. repeat split; reflexivity. Qed.
Lemma layout_le_trans : forall n n' l1 l2 l3, (n <= n')%nat -> layout_le n l1 l2 -> layout_le n' l2 l3 -> layout_le n l1 l3.
Proof.
intros n n' l1 l2 l3 Hn H1 H2. unfold layout_le in *.
destruct H1 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&S1). destruct H2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&S2).
repeat split; try congruence. intros r Hr. rewrite S2 by lia. apply S1, Hr.
Qed.
Definition set_ly_sec (ly : alayout) (r : nat) (a : Z) : alayout :=
ALayout (ly_prim ly) (ly_space ly) (ly_Q ly) (ly_T ly) (ly_C ly) (ly_F ly) (ly_NB ly) (ly_SB ly) (ly_top ly)
(ly_stk_lo ly) (ly_stk_hi ly) (ly_tsd ly) (ly_tr0 ly) (ly_extra ly) (ly_D ly) (ly_vis0 ly) (ly_img ly) (fun r' => if Nat.eqb r' r then a else ly_sec ly r').
Lemma set_ly_sec_le : forall n ly a, layout_le n ly (set_ly_sec ly n a).
Proof.
intros n ly a. repeat split; try reflexivity. intros r Hr. cbn.
destruct (Nat.eqb_spec r n); [lia | reflexivity].
Qed.
Definition shadow_addr (a : Z) : Z := SHADOW_OFF + a / 8.
Arguments shadow_addr _ : simpl never.
Inductive aexp :=
| ANum (z : Z)
| ASp (off : Z)
| AQ (off : Z)
| AT (off : Z)
| AC (off : Z)
| AF (off : Z)
| ANB (off : Z)
| ASB (off : Z)
| ASec (r : nat) (off : Z)
| ATop (off : Z)
| ATsd (off : Z)
| AStk (off : Z)
| AInst (off : Z)
| ADepot (off : Z)
| AStore (off : Z)
| ATp (off : Z)
| AIal (off : Z)
| AD (off : Z)
| ASh (e : aexp).
Inductive aval := AV (e : aexp) | AVmask (mask v : Z).
Record acell := ACell { c_at : aexp; c_w : nat; c_val : aval }.
Definition c8 (a : aexp) (v : aexp) : acell := ACell a 8 (AV v).
Definition c4 (a : aexp) (v : aexp) : acell := ACell a 4 (AV v).
Definition c2 (a : aexp) (v : aexp) : acell := ACell a 2 (AV v).
Definition c1 (a : aexp) (v : aexp) : acell := ACell a 1 (AV v).
Definition z8 (a : aexp) (z : Z) : acell := c8 a (ANum z).
Definition z4 (a : aexp) (z : Z) : acell := c4 a (ANum z).
Definition z2 (a : aexp) (z : Z) : acell := c2 a (ANum z).
Definition z1 (a : aexp) (z : Z) : acell := c1 a (ANum z).
Definition sptr_exp (p : sptr) : aexp :=
match p with
| PNull => ANum 0
| PPrim off => ASp off
| PSec r off => ASec r off
| PFake cid pos => AF (fs_frame_off cid pos)
end.
Definition aoff (e : aexp) (d : Z) : aexp :=
match e with
| ANum z => ANum (z + d) | ASp o => ASp (o + d) | AQ o => AQ (o + d) | AT o => AT (o + d) | AC o => AC (o + d)
| AF o => AF (o + d) | ANB o => ANB (o + d) | ASB o => ASB (o + d) | ASec r o => ASec r (o + d)
| ATop o => ATop (o + d) | ATsd o => ATsd (o + d) | AStk o => AStk (o + d) | AInst o => AInst (o + d)
| ADepot o => ADepot (o + d) | AStore o => AStore (o + d) | ATp o => ATp (o + d) | AIal o => AIal (o + d)
| AD o => AD (o + d)
| ASh e' => ASh (ASh e')
end.
Record acode := ACode {
pc_malloc : Z;
pc_wrap_malloc : Z;
pc_malloc_ra0 : Z;
pc_free : Z;
pc_wrap_free : Z;
pc_free_ra0 : Z;
pc_stack_malloc : Z -> Z;
pc_asan_memcpy : Z;
pc_asan_memset : Z;
pc_wrap_memcpy : Z; pc_wrap_memset : Z; pc_wrap_memcmp : Z; pc_wrap_bcmp : Z;
pc_wrap_read : Z; pc_wrap_fwrite : Z; pc_wrap_vprintf : Z; pc_wrap_vfprintf : Z; pc_wrap_fprintf : Z;
pc_wrap_memchr : Z;
pc_wrap_strnlen : Z;
pc_region_is_poisoned : Z;
pc_spin_mmapdie : Z;
pc_spin_batch : Z;
pc_spin_freearray : Z;
pc_spin_shadow : Z
}.
Record asyms := ASyms {
as_code : acode;
as_inst : Z;
as_gp : Z;
as_tp : Z;
as_tsd : Z;
as_shadow_cell : Z;
as_uar_cell : Z;
as_got_shadow : Z;
as_got_uar : Z;
as_errno : Z;
as_depot : Z;
as_store : Z;
as_ialloc_lo : Z;
as_ialloc_hi : Z;
as_ialloc_w : Z;
as_ialloc_flag : Z;
as_oom_byte : Z;
as_dhash : list Z -> Z;
as_const : alayout -> list acell;
as_junk : alayout -> list (aexp * Z);
as_owned_static : list (Z * Z);
as_zero_shadow : list (Z * Z);
as_universe : list (list Z)
}.
Definition asyms_areas (B : asyms) : list (Z * Z) :=
[(as_inst B, 3632); (as_depot B, 4 * 2 ^ 20 + 32); (as_store B, 32); (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B);
(as_ialloc_flag B, 2); (as_oom_byte B, 1); (as_shadow_cell B, 8); (as_uar_cell B, 4); (as_got_shadow B, 8); (as_got_uar B, 8);
(as_tp B, 60)  ].
Definition zr_sub (r r' : Z * Z) : Prop := fst r' <= fst r /\ fst r + snd r <= fst r' + snd r'.
Record asyms_ok (B : asyms) : Prop := {
aso_static : Forall (fun r => 4096 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) (as_owned_static B);
aso_cover : Forall (fun r => Exists (zr_sub r) (as_owned_static B)) (asyms_areas B);
aso_const_law : forall ly,
In (z8 (ANum (as_shadow_cell B)) SHADOW_OFF) (as_const B ly) /\ In (z4 (ANum (as_uar_cell B)) 1) (as_const B ly) /\
In (z8 (ANum (as_got_shadow B)) (as_shadow_cell B)) (as_const B ly) /\ In (z8 (ANum (as_got_uar B)) (as_uar_cell B)) (as_const B ly);
aso_zshadow : Forall (fun r => 0 <= fst r /\ 0 <= snd r /\ fst r mod 8 = 0 /\ snd r mod 8 = 0 /\ fst r + snd r <= kLowMemEnd) (as_zero_shadow B);
aso_ialloc : as_ialloc_lo B <= as_ialloc_w B /\ as_ialloc_w B + 24 <= as_ialloc_hi B;
aso_cells : 4096 <= as_inst B /\ as_inst B + 3632 <= kLowMemEnd /\ 4096 <= as_depot B /\ as_depot B + 4 * 2 ^ 20 + 32 <= kLowMemEnd /\
4096 <= as_store B /\ as_store B + 32 <= kLowMemEnd /\ 4096 <= as_ialloc_lo B /\ as_ialloc_hi B <= kLowMemEnd /\
4096 <= as_ialloc_flag B /\ as_ialloc_flag B + 2 <= kLowMemEnd /\ 4096 <= as_oom_byte B < kLowMemEnd /\
4096 <= as_tp B - 256 /\ as_tp B + 256 <= kLowMemEnd
}.
Definition o_space : Z := 32.
Definition o_rinfo : Z := 48.
Definition o_sec : Z := 64.
Definition o_sec_chunks : Z := 72.
Definition o_sec_reserved : Z := 112.
Definition o_sec_n : Z := 120.
Definition o_sec_sorted : Z := 128.
Definition o_sec_stats : Z := 136.
Definition o_sec_mutex : Z := 680.
Definition o_comb_stats : Z := 688.
Definition o_quar : Z := 728.
Definition o_q_max : Z := 728 + 64.
Definition o_q_min : Z := 728 + 72.
Definition o_q_maxcache : Z := 728 + 80.
Definition o_q_cmutex : Z := 728 + 152.
Definition o_q_rmutex : Z := 728 + 153.
Definition o_q_size : Z := 728 + 160.
Definition o_q_first : Z := 728 + 168.
Definition o_q_last : Z := 728 + 176.
Definition o_q_bytes : Z := 728 + 184.
Definition t_qc : Z := 80.
Definition t_cache : Z := 208.
Definition t_cache_stats : Z := 208 + 2560.
Definition t_stats : Z := 2800.
Definition t_unwinding : Z := 3168.
Definition d_tab_words : Z := 2 ^ 20.
Definition d_nuniq : Z := 4 * 2 ^ 20.
Definition d_map1 : Z := 4 * 2 ^ 20 + 16.
Definition s_total : Z := 0.
Definition s_block0 : Z := 16.
Section f.
Variable B : asyms.
Variable ly : alayout.
Fixpoint aeval (e : aexp) : Z :=
match e with
| ANum z => z
| ASp off => ly_space ly + off
| AQ off => ly_Q ly + off
| AT off => ly_T ly + off
| AC off => ly_C ly + off
| AF off => ly_F ly + off
| ANB off => ly_NB ly + off
| ASB off => ly_SB ly + off
| ASec r off => ly_sec ly r + off
| ATop off => ly_top ly + off
| ATsd off => ly_tsd ly + off
| AStk off => ly_stk_lo ly + off
| AInst off => as_inst B + off
| ADepot off => as_depot B + off
| AStore off => as_store B + off
| ATp off => as_tp B + off
| AIal off => as_ialloc_lo B + off
| AD off => ly_D ly + off
| ASh e => shadow_addr (aeval e)
end.
Lemma aeval_aoff : forall e d, (forall e', e <> ASh e') -> aeval (aoff e d) = aeval e + d.
Proof. intros e d H. destruct e; try (cbn; rewrite ?Z.add_assoc; reflexivity). exfalso. exact (H e eq_refl). Qed.
Definition sptr_addr (p : sptr) : Z := aeval (sptr_exp p).
Lemma sptr_addr_padd : forall p d, p <> PNull -> (forall c q, p <> PFake c q) -> sptr_addr (padd p d) = sptr_addr p + d.
Proof.
intros p d H1 H2. destruct p; [exfalso; exact (H1 eq_refl) | cbn; lia | cbn; lia | exfalso; exact (H2 _ _ eq_refl)].
Qed.
Definition le_byte (z : Z) (w k : nat) : Z :=
(Z.shiftr (z mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)) mod 256.
Definition reader := Z -> option Z.
Definition cell_holds (rd : reader) (c : acell) : Prop :=
let a := aeval (c_at c) in
match c_val c with
| AV e => forall k, (k < c_w c)%nat -> rd (a + Z.of_nat k) = Some (le_byte (aeval e) (c_w c) k)
| AVmask mask v => exists b, rd a = Some b /\ Z.land b mask = v
end.
Definition range_vis (rd : reader) (r : aexp * Z) : Prop :=
forall i, 0 <= i < snd r -> rd (aeval (fst r) + i) <> None.
Definition range_zero (rd : reader) (r : aexp * Z) : Prop :=
forall i, 0 <= i < snd r -> rd (aeval (fst r) + i) = Some 0.
End f.
Section g.
Context {rc : YM05.RunCeil}.
Definition in_high (lo len : Z) : Prop := kHighMemBeg <= lo /\ lo + len <= ASAN_CEIL.
Definition in_app (lo len : Z) : Prop := 4096 <= lo /\ (lo + len <= kLowShadowBeg \/ (kHighMemBeg <= lo /\ lo + len <= ASAN_CEIL)).
Lemma in_high_app : forall lo len, in_high lo len -> in_app lo len.
Proof. intros lo len [H1 H2]. unfold in_app, kHighMemBeg in *. split; [lia | right; split; [exact H1 | exact H2]]. Qed.
Lemma in_app_sub : forall lo len lo' len', in_app lo len -> lo <= lo' -> 0 <= len' -> lo' + len' <= lo + len -> in_app lo' len'.
Proof. intros lo len lo' len' [H0 H] H1 H2 H3. unfold in_app in *. split; [lia | destruct H as [H|[H4 H5]]; [left; lia | right; lia]]. Qed.
Definition app_addr (a : Z) : Prop := 4096 <= a /\ (a < kLowShadowBeg \/ (kHighMemBeg <= a /\ a < ASAN_CEIL)).
Lemma in_app_addr : forall lo len a, in_app lo len -> lo <= a < lo + len -> app_addr a.
Proof. intros lo len a [H0 [HL | [HH1 HH2]]] Ha; unfold app_addr; split; [lia | | lia |]; [left; lia | right; lia]. Qed.
Lemma app_addr_below_ceil : forall a, app_addr a -> 4096 <= a < ASAN_CEIL.
Proof. intros a [H0 H]. pose proof ASAN_CEIL_range as [CR _]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Definition in_band_rw (a : Z) : Prop := (kLowShadowBeg <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd).
Lemma shadow_addr_in_band : forall lo len i, in_app lo len -> 0 <= i < len -> in_band_rw (shadow_addr (lo + i)).
Proof.
intros lo len i [H0 [HL | [HH1 HH2]]] Hi; pose proof ASAN_CEIL_range as [CR _];
unfold in_band_rw, shadow_addr, SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; [left | right]; split; lia.
Qed.
Definition page_aligned (a : Z) : Prop := a mod 4096 = 0.
Definition owned_extents (ly : alayout) : list (Z * Z) :=
[(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize);
(ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256)  ;
(ly_D ly, 4096)  ].
Definition static_extents (ly : alayout) : list (Z * Z) :=
owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly  ].
Definition zdisjoint (a b : Z * Z) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pairwise {X : Type} (R : X -> X -> Prop) (l : list X) : Prop :=
match l with [] => True | x :: t => Forall (R x) t /\ pairwise R t end.
Definition vis0_zones (ly : alayout) : list (Z * Z) :=
[(ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize); (ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize);
(ly_C ly, kCtxMapSize); (ly_D ly, 4096); (ly_Q ly, kPtrArrayResv); (ly_space ly + kRegionInfoOff, 4096); ly_img ly  ]
++ ly_extra ly.
Record layout_ok (ly : alayout) : Prop := {
lo_prim_al : page_aligned (ly_prim ly);
lo_space_al : ly_space ly mod 65536 = 0;
lo_space_in : ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize;
lo_Q_al : page_aligned (ly_Q ly);
lo_T_al : page_aligned (ly_T ly);
lo_F_al : page_aligned (ly_F ly);
lo_NB_al : page_aligned (ly_NB ly);
lo_SB_al : page_aligned (ly_SB ly);
lo_C_al : ly_C ly mod 8 = 0;
lo_tsd_al : ly_tsd ly mod 8 = 0;
lo_high : in_high (ly_prim ly) kPrimResvSize;
lo_app : Forall (fun e => in_app (fst e) (snd e)) (owned_extents ly);
lo_img : fst (ly_img ly) = kImgLo /\ 0 < snd (ly_img ly) /\ kImgLo + snd (ly_img ly) <= kImgEnd /\ page_aligned (snd (ly_img ly));
lo_disj : pairwise zdisjoint (static_extents ly);
lo_top : ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly <= ly_stk_hi ly /\ page_aligned (ly_top ly) /\
ly_stk_hi ly <= kHighMemEnd /\ page_aligned (ly_stk_lo ly) /\ page_aligned (ly_stk_hi ly) /\
kHighMemBeg <= ly_stk_lo ly;
lo_tr0 : (1 <= length (ly_tr0 ly) <= 31)%nat;
lo_extra : (length (ly_extra ly) <= 8)%nat /\
Forall (fun e => page_aligned (fst e) /\ 0 < snd e <= 2 ^ 24 /\ 4096 <= fst e /\ fst e + snd e <= ASAN_CEIL /\
(fst e + snd e <= kLowShadowBeg \/ kHighMemBeg <= fst e)) (ly_extra ly) /\
pairwise zdisjoint (ly_extra ly ++ static_extents ly);
lo_D_al : page_aligned (ly_D ly);
lo_ctx : zdisjoint (ly_C ly, kCtxMapSize) (ly_prim ly, kPrimResvSize);
lo_vis0 : Forall (fun v => Exists (fun z => shadow_addr (fst z) <= fst v /\ fst v + snd v <= shadow_addr (fst z + snd z - 1) + 1) (vis0_zones ly))
(ly_vis0 ly);
lo_stk_ceil : ASAN_CEIL <= ly_stk_lo ly
}.
Definition region_base (ly : alayout) (c : Z) : Z := ly_space ly + region_off c.
Definition fa_base (ly : alayout) (c : Z) : Z := ly_space ly + region_off c + kFreeArrayOffset.
Definition rinfo_addr (ly : alayout) (c : Z) : Z := ly_rinfo ly + 128 * c.
Definition cache_addr (ly : alayout) (c : Z) : Z := ly_T ly + t_cache + 80 * c.
Definition frame_addr (ly : alayout) (cid pos : Z) : Z := ly_F ly + fs_frame_off cid pos.
Definition flag_addr (ly : alayout) (cid pos : Z) : Z := ly_F ly + fs_flag_off cid pos.
End g.
