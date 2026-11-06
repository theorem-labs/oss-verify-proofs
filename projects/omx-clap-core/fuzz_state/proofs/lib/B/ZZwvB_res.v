(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v; 469 of its 545 lines of code are new or changed and 346 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cind.v, with its module paths, module names and numbers changed; 248 of its 297 lines of code are new or changed and 496 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_res.v (a working branch
   1a5dc5b2e7c): same lemma names; adapted to image B's frame (WVC_F = 192, the entry d in the frame slot 24, so
   wvc_cs0 names xatom 4), B's loop registers (ZZwvB_defs.wvc_Lregs), B's atom facts (wvc_gfA / wvc_gfK carry facts on
   s5 = i, kids and keys, so wvc_resume_rs takes the premises they need), B's open state (the plain fss_retT, so
   wvc_ssO_ret is the identity) and the close-point state (the new wvc_ssN_ret); the root node's place facts come from
   FSW_write_value_entry.wv_pobj (lib/B's FSH_Fn_reader.pobj); imports point at lib/B's image files and walk kit.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B. *)
(* write_value's CONTAINER arms (fs.asan-ubsan image B, write_value 0x84010): the RESUMED STATE of the container loop.
   - wvc_resume_rs / wvc_resume_rs0: the extra regions (the node at atom 9, the object's key slot), the whole region
     list's disjointness, the atom facts and the shadow entries of a loop state and of the open state, from the facts at
     the call (the entry's pattern: FSW_write_value_entry.wv_entry);
   - wvc_csL_after / wvc_cs0_after: the frame chunks across a callee call (its wkeep), moved to the return env;
     wvc_csL_in / wvc_cs0_in / wvc_rsL_wf / wvc_rs0_wf: the chunk and region side facts the resume asks;
   - wvc_ssL_ret / wvc_ssO_ret / wvc_ssN_ret: from the plain resumed state FSW_write_value_entry.wvc_after_call_ot
     gives to the loop state (registers and the two conditions), to the open state and to the close-point state.
   Template (not a copied proof): lib/A/ZZwv_res.v; FSW_write_value_entry.v wv_entry (disjointness, atoms, shadow
   entries), ZZwvB_runs1.v wvc_seg_open_ind (the two conditions).
   Rule 24 (proof-index, a Theorem Labs lane 04:2xZ, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSupoisonStack.
(* FSH_Fn_reader is lib/B's (Required below, used qualified) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_pj
FSH_Fn_writer FSW_write_value_entry ZZwvB_defs ZZwvB_inv ZZwvB_kit ZZwvB_call ZZwvB_call2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- two ranges are apart: an image range and a range of non-image bytes (FSW_write_value_entry.wv_apart_img's
   statement and proof), or two ranges no byte of which is shared ---- *)
Lemma wvr_apart_img : forall c n v k,
  0 < n -> 0 < k -> (forall a, c <= a < c + n -> in_img tfibsegs a) -> (forall a, v <= a < v + k -> ~ in_img tfibsegs a) ->
  v + k <= c \/ c + n <= v.
Proof.
intros c n v k Hn Hk Hc Hv. destruct (Z_le_gt_dec (v + k) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + n) v) as [L2|L2]; [right; exact L2|]. exfalso.
apply (Hv (Z.max v c)); [lia|]. apply Hc. lia.
Qed.
Lemma wvr_apart_pt : forall a n b k,
  0 < n -> 0 < k -> (forall x, a <= x < a + n -> ~ (b <= x < b + k)) -> a + n <= b \/ b + k <= a.
Proof.
intros a n b k Hn Hk H. destruct (Z_le_gt_dec (a + n) b) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (b + k) a) as [L2|L2]; [right; exact L2|]. exfalso.
apply (H (Z.max a b)); lia.
Qed.

(* ---- a chunk read at one env and memory is the same chunk at another env and memory that agree on its bytes
   (FSW_put.fsw_pf_chunk_move's argument, at the same base) ---- *)
Lemma wvr_chunk_move : forall E E' (m m' : word -> option byte) b c,
  YP09.chunk_ok tfibsegs E m b c ->
  (forall i, 0 <= i < YP09.c_len c ->
     YP09.cbyte tfibsegs E' (b + YP09.c_off c) (YP09.c_val c) i = YP09.cbyte tfibsegs E (b + YP09.c_off c) (YP09.c_val c) i) ->
  (forall i, 0 <= i < YP09.c_len c ->
     mbyte tfibsegs m' (b + YP09.c_off c + i) = mbyte tfibsegs m (b + YP09.c_off c + i)) ->
  YP09.chunk_ok tfibsegs E' m' b c.
Proof.
intros E E' m m' b c Hc Hv Hm i Hi.
destruct (Hc i Hi) as (x & Hx & Hmx).
exists x. rewrite (Hv i Hi), (Hm i Hi). split; [exact Hx | exact Hmx].
Qed.

(* ================= the frame chunks: inside the frame, well formed, kept across a call ================= *)
Lemma wvc_csL_in : forall p, Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= WVC_F) (wvc_csL p).
Proof.
intros p. unfold wvc_csL, wvc_cs0, WVC_F. cbn [seq map app].
repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.c_off YP09.c_len YP09.c_val YP09.cv_len Z.of_N Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
Lemma wvc_cs0_in : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= WVC_F) wvc_cs0.
Proof.
unfold wvc_cs0, WVC_F. cbn [seq map app].
repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.c_off YP09.c_len YP09.c_val YP09.cv_len Z.of_N Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma wvc_rsL_wf : forall ty p, ty = 5 \/ ty = 6 -> regions_wf (fsT_ret_regions WVC_F (wvc_csL p) (wvc_rsL ty)) = true.
Proof. intros ty p [-> | ->]; vm_compute; reflexivity. Qed.
Lemma wvc_rs0_wf : forall ty, regions_wf (fsT_ret_regions WVC_F wvc_cs0 [wvc_node ty]) = true.
Proof. intros ty. vm_compute. reflexivity. Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the frame chunks across a callee call: the callee keeps [spc, ot) apart from the object [o, o + 32), so the frame
   [sp - WVC_F, sp) below o keeps its bytes; the return env agrees on the atoms the chunks name (atom 9, the shadow
   base, xatom 4 = d and the saved registers xatom 5 .. 17) *)
Lemma wvc_csL_after : forall E E' (W W' : world tfibsegs) m m' sp spc ot o p,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (sp - WVC_F)) (wvc_csL p) ->
  wkeep tfibsegs W W' m m' spc ot o 32 -> spc <= sp - WVC_F -> sp <= o -> o + 32 <= ot ->
  ew E' 9 = ew E 9 -> ew E' 32 = ew E 32 -> (forall j, (4 <= j <= 17)%nat -> ew E' (xatom j) = ew E (xatom j)) ->
  Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W') m') (sp - WVC_F)) (wvc_csL p).
Proof.
intros E E' W W' m m' sp spc ot o p HC HK Hs Ho Hot E9 E32 HX.
apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) HC c Hc) as Hck.
pose proof (proj1 (Forall_forall _ _) (wvc_csL_in p) c Hc) as (Hc0 & Hc1).
assert (KB : forall i, 0 <= i < YP09.c_len c ->
  mbyte tfibsegs (rdW W' m') (sp - WVC_F + YP09.c_off c + i) = mbyte tfibsegs (rdW W m) (sp - WVC_F + YP09.c_off c + i)).
{ intros i Hi. exact (proj1 (HK (sp - WVC_F + YP09.c_off c + i) ltac:(lia) ltac:(lia))). }
clear HC Hc0 Hc1 HK.
unfold wvc_csL, wvc_cs0 in Hc. cbn [seq map app In] in Hc.
repeat (destruct Hc as [<- | Hc]); [..| destruct Hc].
all: apply (wvr_chunk_move E E' _ _ _ _ Hck); [|exact KB].
all: intros i _; cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot wvc_shv]; rewrite ?E9, ?E32;
  try (rewrite HX by lia); reflexivity.
Qed.

(* image B's wvc_cs0 holds the entry d (xatom 4) at slot 24, so the env agreement starts at xatom 4 *)
Lemma wvc_cs0_after : forall E E' (W W' : world tfibsegs) m m' sp spc ot o,
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (sp - WVC_F)) wvc_cs0 ->
  wkeep tfibsegs W W' m m' spc ot o 32 -> spc <= sp - WVC_F -> sp <= o -> o + 32 <= ot ->
  ew E' 9 = ew E 9 -> ew E' 32 = ew E 32 -> (forall j, (4 <= j <= 17)%nat -> ew E' (xatom j) = ew E (xatom j)) ->
  Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W') m') (sp - WVC_F)) wvc_cs0.
Proof.
intros E E' W W' m m' sp spc ot o HC HK Hs Ho Hot E9 E32 HX.
apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) HC c Hc) as Hck.
pose proof (proj1 (Forall_forall _ _) wvc_cs0_in c Hc) as (Hc0 & Hc1).
assert (KB : forall i, 0 <= i < YP09.c_len c ->
  mbyte tfibsegs (rdW W' m') (sp - WVC_F + YP09.c_off c + i) = mbyte tfibsegs (rdW W m) (sp - WVC_F + YP09.c_off c + i)).
{ intros i Hi. exact (proj1 (HK (sp - WVC_F + YP09.c_off c + i) ltac:(lia) ltac:(lia))). }
clear HC Hc0 Hc1 HK.
unfold wvc_cs0 in Hc. cbn [seq map app In] in Hc.
repeat (destruct Hc as [<- | Hc]); [..| destruct Hc].
all: apply (wvr_chunk_move E E' _ _ _ _ Hck); [|exact KB].
all: intros i _; cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot wvc_shv]; rewrite ?E9, ?E32;
  try (rewrite HX by lia); reflexivity.
Qed.

(* ================= the resumed regions, facts and shadow entries ================= *)
(* the open state (and any state with the node alone): the node's region, the five regions apart, atom 9's fact, the
   node's shadow entry *)
Lemma wvc_resume_rs0 : forall ly S U (W : world tfibsegs) mem md E ty cs v num str kids keys n cap sp,
  ARU tfibsegs B ly S U W mem md -> FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  bv_unsigned (ew E 2) = sp - WVC_F -> alloc_ceiling <= sp - WVC_F -> sp <= 2 ^ 47 ->
  ew E 9 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E (xatom 0) = Z_to_bv 64 str -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n ->
  Forall (YP09.region_ok tfibsegs E (mrestrict (w_H W) mem)) [wvc_node ty] /\
  pairwise_disjoint E (fsT_ret_regions WVC_F cs [wvc_node ty]) /\
  atoms_ok E wvc_gf0 /\ sh_ok tfibsegs fs_Bx wvc_SH0 E (mrestrict (w_H W) mem).
Proof.
intros ly S UU W mem md E ty cs v num str kids keys n cap sp HARU HPO HH E2sp Hceil Hsp E9 E32 E0 E1 E2 E3.
pose proof (proj1 HARU) as HAR.
pose proof asan_consts as (C1 & _).
destruct (wv_pobj B ly S W _ md mem v HAR HPO) as (Hv4096 & Hvceil & Hv8 & Hvimg & _).
assert (U32 : U E fs_Bx = SHADOW_OFF) by exact (wvc_U32 E E32).
assert (U9 : U E (SOff 9 0) = v) by (apply U_atom; [exact E9 | lia]).
split; [|split; [|split]].
- constructor; [|constructor].
  exact (wvc_node_ok E (rdW W mem) v ty num str kids keys n cap HH E9 E0 E1 E2 E3).
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, wvc_node, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2sp, E9, (unsigned_lit_small v) by lia.
  pose proof (wvr_apart_img tfib_D_GOT_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D1.
  pose proof (wvr_apart_img tfib_D_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, WVC_F in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold wvc_gf0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 3) with 8. unfold WVC_CEIL.
  split; [|exact I]. split; [lia|]. split; [exact Hv8 | lia].
- constructor; [|constructor].
  exact (wvc_node_sh B ly S W _ md mem v E HAR HPO U32 U9).
Qed.

(* a loop state: the node (array) or the node and the key slot (object). Image B's loop facts (wvc_gfA / wvc_gfK) also
   bound s5 = i (atom 21), kids (xatom 1) and, for the object, keys (xatom 2): the premises on i, kids and keys *)
Lemma wvc_resume_rs : forall ly S U (W : world tfibsegs) mem md E ty p v num str kids keys n cap sp ke key i,
  ty = 5 \/ ty = 6 ->
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  bv_unsigned (ew E 2) = sp - WVC_F -> alloc_ceiling <= sp - WVC_F -> sp <= 2 ^ 47 ->
  ew E 9 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E (xatom 0) = Z_to_bv 64 str -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n ->
  ew E 21 = Z_to_bv 64 i -> 0 <= i < 2 ^ 54 -> 4096 <= kids <= WVC_CEIL ->
  (ty = 6 -> 4096 <= keys <= WVC_CEIL) ->
  (ty = 6 -> ew E (xatom 18) = Z_to_bv 64 ke /\ ew E (xatom 19) = Z_to_bv 64 key /\
     PjStruct.pj_u64 tfibsegs (mrestrict (w_H W) mem) ke key /\
     (exists P q, In (P, q) (ablocks B ly S) /\ P + 16 <= ke /\ ke + 8 <= P + req_size q) /\ ke mod 8 = 0 /\
     (forall x, ke <= x < ke + 8 -> ~ (v <= x < v + 56))) ->
  Forall (YP09.region_ok tfibsegs E (mrestrict (w_H W) mem)) (wvc_rsL ty) /\
  pairwise_disjoint E (fsT_ret_regions WVC_F (wvc_csL p) (wvc_rsL ty)) /\
  atoms_ok E (wvc_gfL ty) /\
  sh_ok tfibsegs fs_Bx (wvc_SHL ty) E (mrestrict (w_H W) mem).
Proof.
intros ly S UU W mem md E ty p v num str kids keys n cap sp ke key i Hty HARU HFH HPO HH E2sp Hceil Hsp E9 E32
  E0 E1 E2 E3 E21 Hi Hkids Hkeys HK.
assert (A21 : afact_ok E 21 (mkAF 0 (2 ^ 54 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E21, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
assert (A1 : afact_ok E (xatom 1) (mkAF 4096 WVC_CEIL 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. unfold WVC_CEIL in *. rewrite E1, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
destruct Hty as [-> | ->].
{ change (wvc_rsL 5) with [wvc_node 5]. change (wvc_gfL 5) with wvc_gfA. change (wvc_SHL 5) with wvc_SH0.
  destruct (wvc_resume_rs0 ly S UU W mem md E 5 (wvc_csL p) v num str kids keys n cap sp HARU HPO HH E2sp Hceil Hsp
    E9 E32 E0 E1 E2 E3) as (R1 & R2 & R3 & R4).
  split; [exact R1|]. split; [exact R2|]. split; [|exact R4].
  unfold wvc_gfA. cbn [atoms_ok]. split; [exact A21|]. split; [exact A1 | exact R3]. }
specialize (Hkeys eq_refl).
destruct (HK eq_refl) as (E18 & E19 & Hu & (P & q & Hin & Hk1 & Hk2) & Hk8 & Hkv). clear HK.
change (wvc_rsL 6) with [wvc_node 6; wvc_keyR]. change (wvc_gfL 6) with wvc_gfK. change (wvc_SHL 6) with wvc_SHK.
pose proof (proj1 HARU) as HAR.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _).
destruct (wv_pobj B ly S W _ md mem v HAR HPO) as (Hv4096 & Hvceil & Hv8 & Hvimg & _).
destruct (fsw_ablock_low B ly S W _ md P q HAR Hin) as (HP4096 & HPceil & _).
assert (Hkimg : forall a, ke <= a < ke + 8 -> ~ in_img tfibsegs a).
{ intros a Ha. exact (blk_img tfibsegs B LAWS ly S W _ md P q a HAR Hin ltac:(lia)). }
assert (U32 : U E fs_Bx = SHADOW_OFF) by exact (wvc_U32 E E32).
assert (U9 : U E (SOff 9 0) = v) by (apply U_atom; [exact E9 | lia]).
assert (U18 : U E (SOff (xatom 18) 0) = ke) by (apply U_atom; [exact E18 | lia]).
split; [|split; [|split]].
- constructor; [|constructor; [|constructor]].
  + exact (wvc_node_ok E (rdW W mem) v 6 num str kids keys n cap HH E9 E0 E1 E2 E3).
  + exact (wvc_keyR_ok E (rdW W mem) ke key Hu E18 E19 ltac:(lia) ltac:(lia)).
- apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, wvc_node, wvc_keyR, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E2sp, E9, E18, (unsigned_lit_small v), (unsigned_lit_small ke) by lia.
  pose proof (wvr_apart_img tfib_D_GOT_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D1.
  pose proof (wvr_apart_img tfib_D_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D2.
  pose proof (wvr_apart_img tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ke 8 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hkimg) as D3.
  pose proof (wvr_apart_img tfib_D_asan_shadow_memory_dynamic_address 8 ke 8 ltac:(lia) ltac:(lia)
    (wvc_img_cover tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hkimg) as D4.
  pose proof (wvr_apart_pt ke 8 v 56 ltac:(lia) ltac:(lia) Hkv) as D5.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, WVC_F in *.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold wvc_gfK, wvc_gfA. cbn [atoms_ok].
  split; [|split; [|split; [|split; [exact A21 | split; [exact A1 |]]]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E18, (unsigned_lit_small ke) by lia.
    change (2 ^ 3) with 8. unfold WVC_CEIL. split; [lia | split; [exact Hk8 | lia]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. pose proof (u64_range (ew E (xatom 19))) as R19.
    rewrite Z.pow_0_r, Z.mod_1_r. split; [lia | split; [reflexivity | lia]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. unfold WVC_CEIL in *. rewrite E2, (unsigned_lit_small keys) by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
  + unfold wvc_gf0. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, (unsigned_lit_small v) by lia. change (2 ^ 3) with 8. unfold WVC_CEIL.
    split; [|exact I]. split; [lia|]. split; [exact Hv8 | lia].
- constructor; [|constructor; [|constructor]].
  + exact (wvc_node_sh B ly S W _ md mem v E HAR HPO U32 U9).
  + exact (wvc_keyR_sh B ly S UU W mem md ke E P q HARU HFH Hin Hk1 Hk2 U32 U18).
Qed.

(* ================= from the plain resumed state to the loop state, the open state and the close-point state ======== *)
(* the loop registers of ZZwvB_defs.wvc_Lregs (s2 = 18, s4 = 20, s6 = 22, s8 = 24, s9 = 25, s10 = 26, s11 = 27) and
   the two conditions (pretty, n <> 0) *)
Lemma wvc_ssL_ret : forall E ty p r ms n,
  st_ok tfibsegs E (fss_retT r WVC_F (wvc_csL p) (wvc_rsL ty) (wvc_gfL ty)) ms ->
  YK11.getr (ms_regs ms) 18%bv = sv_denot E (SOff 9 40) ->
  YK11.getr (ms_regs ms) 20%bv = sv_denot E (wvc_shv 9 24) ->
  YK11.getr (ms_regs ms) 22%bv = sv_denot E (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) ->
  YK11.getr (ms_regs ms) 24%bv = sv_denot E (SOff 9 24) ->
  YK11.getr (ms_regs ms) 25%bv = sv_denot E (SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0)) ->
  YK11.getr (ms_regs ms) 26%bv = sv_denot E (SLit 0) ->
  YK11.getr (ms_regs ms) 27%bv = sv_denot E (wvc_shv 9 40) ->
  ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> ew E (xatom 3) = Z_to_bv 64 n -> 0 < n < 2 ^ 64 ->
  st_ok tfibsegs E (wvc_ssL ty p r) ms.
Proof.
intros E ty p r ms n HS R18 R20 R22 R24 R25 R26 R27 E19 Hp En Hn.
unfold wvc_ssL.
apply st_ok_add_cond.
2: { rewrite branch_ne_U, U_SLit, (U_atom E (xatom 3) n En) by lia.
     change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. lia. }
apply st_ok_add_cond.
2: { destruct (Z.eqb_spec p 0) as [->|Hp0]; cbv beta iota.
     - rewrite branch_eq_U, U_SLit, (U_atom E 19 0 E19) by lia. vm_compute. reflexivity.
     - rewrite branch_ne_U, U_SLit, (U_atom E 19 p E19) by lia.
       change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hp0. }
apply wvc_st_ok_setr; [exact HS|].
unfold wvc_Lregs.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | assumption]).
Qed.

(* image B's open state is the plain resumed state (no register setting) *)
Lemma wvc_ssO_ret : forall E ty ms,
  st_ok tfibsegs E (fss_retT WVC_R_OPEN WVC_F wvc_cs0 [wvc_node ty] wvc_gf0) ms ->
  st_ok tfibsegs E (wvc_ssO ty) ms.
Proof. intros E ty ms HS. exact HS. Qed.

(* the close-point state (after the closing indent): the node alone, the same registers and conditions *)
Lemma wvc_ssN_ret : forall E ty p ms n,
  st_ok tfibsegs E (fss_retT WVC_R_CLOSE WVC_F (wvc_csL p) [wvc_node ty] wvc_gf0) ms ->
  YK11.getr (ms_regs ms) 18%bv = sv_denot E (SOff 9 40) ->
  YK11.getr (ms_regs ms) 20%bv = sv_denot E (wvc_shv 9 24) ->
  YK11.getr (ms_regs ms) 22%bv = sv_denot E (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) ->
  YK11.getr (ms_regs ms) 24%bv = sv_denot E (SOff 9 24) ->
  YK11.getr (ms_regs ms) 25%bv = sv_denot E (SAlu ALU_SUB (SOff (xatom 18) 0) (SOff (xatom 2) 0)) ->
  YK11.getr (ms_regs ms) 26%bv = sv_denot E (SLit 0) ->
  YK11.getr (ms_regs ms) 27%bv = sv_denot E (wvc_shv 9 40) ->
  ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> ew E (xatom 3) = Z_to_bv 64 n -> 0 < n < 2 ^ 64 ->
  st_ok tfibsegs E (wvc_ssN ty p) ms.
Proof.
intros E ty p ms n HS R18 R20 R22 R24 R25 R26 R27 E19 Hp En Hn.
unfold wvc_ssN.
apply st_ok_add_cond.
2: { rewrite branch_ne_U, U_SLit, (U_atom E (xatom 3) n En) by lia.
     change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. lia. }
apply st_ok_add_cond.
2: { destruct (Z.eqb_spec p 0) as [->|Hp0]; cbv beta iota.
     - rewrite branch_eq_U, U_SLit, (U_atom E 19 0 E19) by lia. vm_compute. reflexivity.
     - rewrite branch_ne_U, U_SLit, (U_atom E 19 p E19) by lia.
       change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hp0. }
apply wvc_st_ok_setr; [exact HS|].
unfold wvc_Lregs.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | assumption]).
Qed.

End R.
