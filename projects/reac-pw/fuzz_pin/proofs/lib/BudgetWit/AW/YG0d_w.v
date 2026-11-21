(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0d.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YG0d.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 DepotCfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ESTACK : Z := 4096.
Definition acallee_saved (r : Z) : Prop :=
r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27).
Definition aregs_preserved (regs regs' : bvmap 5 word) : Prop :=
forall r, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition spZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 2).
Definition raZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 1).
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition rdword (rd : reader) (a : Z) : option Z :=
match rd a, rd (a+1), rd (a+2), rd (a+3), rd (a+4), rd (a+5), rd (a+6), rd (a+7) with
| Some b0, Some b1, Some b2, Some b3, Some b4, Some b5, Some b6, Some b7 =>
Some (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))
| _, _, _, _, _, _, _, _ => None
end.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Let code := as_code B.
Definition cfg_at (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
mkCfg (mkst regs (w64 pc) mem (seg_rom segs)) md.
Definition ecall_pre (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR segs B ly S W mem md /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Definition shadow_hull_vis (rd : reader) (x n : Z) : Prop :=
forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s <> None.
Definition dest_ok (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (d n : Z) : Prop :=
forall a, d <= a < d + n -> writable_at segs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a /\ ~ (spZ regs - ESTACK <= a < spZ regs).
Definition src_ok (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (s n : Z) : Prop :=
forall a, s <= a < s + n -> aview segs (w_H W) mem a <> None /\ ~ (spZ regs - ESTACK <= a < spZ regs).
Inductive memop := OCpy | OSet.
Definition amem_range (p n : Z) : Prop := p + n <= kLowMemEnd - 1 \/ (kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1).
Definition aintrin_realizes (op : memop) (pc : Z) : Prop :=
forall ly S W regs mem md d x n,
ecall_pre ly S W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Definition first_byte (W : world segs) (mem : word -> option byte) (x n c k : Z) : Prop :=
0 <= k <= n /\
(forall i, 0 <= i < k -> exists b, aview segs (w_H W) mem (x + i) = Some b /\ b <> c) /\
(k < n -> aview segs (w_H W) mem (x + k) = Some c).
Definition ablocks (ly : alayout) (S : astate) : list (Z * Z) :=
map (fun b => (sptr_addr B ly (fst b), snd b)) (blocks S).
Definition AR_blocks_law : Prop :=
forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks ly S)) /\
0 <= n < MALLOC_MAX.
Definition AR_shadow_law : Prop :=
forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks ly S) ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF p (req_size n) /\
shadow_hull_vis (aview segs (w_H W) mem) p (req_size n).
Definition AR_zshadow_law : Prop :=
forall ly S W mem md r,
AR segs B ly S W mem md -> In r (zero_shadow_ranges B ly) ->
zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r).
Definition AR_frame_law : Prop :=
forall ly S W mem md mem' md',
AR segs B ly S W mem md ->
(forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
(forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
AR segs B ly S W mem' md'.
Definition AR_frames_law : Prop :=
forall ly S W mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 32 = 0 /\ in_app (frame_addr ly cid pos) (fs_frame_bytes cid) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
(forall i, 0 <= i < fs_frame_bytes cid / 8 ->
apresent (w_H W) mem (shadow_addr (frame_addr ly cid pos) + i) /\
~ aowned B ly S (shadow_addr (frame_addr ly cid pos) + i)).
Definition AR_flag_law : Prop :=
forall ly S (W : world segs) mem md cid pos,
AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Definition AR_const_law : Prop :=
forall ly S W mem md,
AR segs B ly S W mem md ->
rdword (aview segs (w_H W) mem) (as_shadow_cell B) = Some SHADOW_OFF /\
rd32 (aview segs (w_H W) mem) (as_uar_cell B) 1 /\
rdword (aview segs (w_H W) mem) (as_got_shadow B) = Some (as_shadow_cell B) /\
rdword (aview segs (w_H W) mem) (as_got_uar B) = Some (as_uar_cell B).
Definition AR_stack_law : Prop :=
forall ly S W mem md a,
AR segs B ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ aowned B ly S a.
Definition in_img (a : Z) : Prop := exists sg, In sg segs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Definition AR_owned_low_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> aowned B ly S a -> 0 <= a < alloc_ceiling.
Definition AR_owned_image_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md -> in_img a -> (aowned B ly S a <-> Exists (in_zr a) (as_owned_static B)).
Definition AR_sep_law : Prop :=
forall ly S W mem md, AR segs B ly S W mem md ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks ly S)
++ map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) (frames S)) /\
Forall (fun f => 4096 <= frame_addr ly (fst f) (snd f) /\ frame_addr ly (fst f) (snd f) + fs_frame_bytes (fst f) <= alloc_ceiling) (frames S).
Definition AR_layout_law : Prop :=
forall ly S W mem md ly',
AR segs B ly S W mem md -> layout_le (length (st_secs S)) ly ly' ->
ablocks ly' S = ablocks ly S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) /\
(forall a, aowned B ly' S a <-> aowned B ly S a).
Definition AR_wle_law : Prop :=
forall ly S W W' mem md,
AR segs B ly S W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) ->
A_bytes (w_A W') <= abudget S -> AR segs B ly S W' mem md.
Definition AR_client_img_law : Prop :=
forall ly S W mem md a, AR segs B ly S W mem md ->
((exists p n, In (p, n) (ablocks ly S) /\ p <= a < p + req_size n) \/
(exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) \/
(exists cid pos, In (cid, pos) (frames S) /\ a = flag_addr ly cid pos)) ->
~ in_zr a (ly_img ly) /\ ~ in_img a.
Record AR_laws : Prop := {
al_blocks : AR_blocks_law;
al_shadow : AR_shadow_law;
al_zshadow : AR_zshadow_law;
al_frame : AR_frame_law;
al_frames : AR_frames_law;
al_flag : AR_flag_law;
al_const : AR_const_law;
al_stack : AR_stack_law;
al_wle : AR_wle_law;
al_layout : AR_layout_law;
al_owned_low : AR_owned_low_law;
al_owned_image : AR_owned_image_law;
al_sep : AR_sep_law;
al_client_img : AR_client_img_law
}.
End j.
End g.
