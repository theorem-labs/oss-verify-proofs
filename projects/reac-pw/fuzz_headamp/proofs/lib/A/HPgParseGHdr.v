(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: kept_run and same_io_wvb of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at
   5eaa5614305, awr_stk of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at fb6520a9cda, U_sext32_small of
   proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v at b0f706c04a1 and U_sx32_eqb of proofs/libreac/fuzz_knock/lib/A/APgStep.v
   at 6ebe35ba632, renamed (kept_run_pe, same_io_wvb_pe, pe_awr, pe_U_sx32, pe_U_sx32_eqb); pe_awr also reads sp's value
   through the token atoms a run adds; everything else below is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseE.v, with its module paths changed; 277 of its 349 lines of code are new or changed and 477 lines of the source are left out. *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT pieces of segment E of reac_headamp_prop_parse_result's walks in both
   ASan images (image A lib/A/HPgParseE.v, image B lib/AU/HPgParseE.v), from the hole's opening to EPI and FIND: the
   model at the exits of the header tests (Pod/Spa.v is_object_type's four tests, find_prop at r = 16), the engine
   forms of the size and type tests (the sign-extended 32-bit loads), the three zero words of res and where res lies,
   the pod's three header words in the cut env (slots 47, 48, 49), regions at a pointer, and hp_core from its pieces.
   No image numeral: every lemma is over segs with the one Section hypothesis segs_low. Proves no function
   (kind: segment lemma).

   What both images do the same way after the open (measured on the neutral listings of both): `beqz s1` (res = 0
   skips the res words), the three instrumented `sw zero` at res, res + 4, res + 8, `li s4,-1`, `beqz a0` (NULL),
   the instrumented 4-byte loads of the size at P, the type at P + 4 and the object type at P + 8, the tests
   size >> 20 <> 0, size <u 8, type <> 15, object type <> 0x40002 (each -> EPI with -1), size <u 16 (-> `li s4,0`,
   EPI), and the find setup a0 = P + 8, a1 = P + 16, a2 = size - 16, a3 = P + size - 8, a4 = 0x80001, s4 = 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseGKit HPgParseGWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= outside any image ======================================= *)
(* the float state as its two fields: a segment's goal at the entry's fx, the cuts at mkFP F fc *)
Lemma hgh_fx_eta : forall f : YK11.FPState, mkFP (@fp_regs f) (@fp_csr f) = f.
Proof. intros [F C]. reflexivity. Qed.

(* ---------------------------------- the four tests of spa_pod_is_object_type ---------------------------------- *)
Lemma hgh_obj_eq : forall bs,
Spa.is_object_type bs Model.POD_OBJECT_PROPS =
(Spa.u32_at bs 0 <? 1048576) && (Spa.u32_at bs 4 =? 15) && (8 <=? Spa.u32_at bs 0) && (Spa.u32_at bs 8 =? 262146).
Proof. reflexivity. Qed.

Lemma hgh_obj_big : forall bs, 1048576 <= Spa.u32_at bs 0 ->
Spa.is_object_type bs Model.POD_OBJECT_PROPS = false.
Proof. intros bs H. rewrite hgh_obj_eq. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.

Lemma hgh_obj_small : forall bs, Spa.u32_at bs 0 < 8 ->
Spa.is_object_type bs Model.POD_OBJECT_PROPS = false.
Proof. intros bs H. rewrite hgh_obj_eq. rewrite (proj2 (Z.leb_gt _ _) H), andb_false_r. reflexivity. Qed.

Lemma hgh_obj_type : forall bs, Spa.u32_at bs 4 <> 15 ->
Spa.is_object_type bs Model.POD_OBJECT_PROPS = false.
Proof. intros bs H. rewrite hgh_obj_eq. rewrite (proj2 (Z.eqb_neq _ _) H), !andb_false_r. reflexivity. Qed.

Lemma hgh_obj_props : forall bs, Spa.u32_at bs 8 <> 262146 ->
Spa.is_object_type bs Model.POD_OBJECT_PROPS = false.
Proof. intros bs H. rewrite hgh_obj_eq. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity. Qed.

Lemma hgh_obj_true : forall bs, Spa.u32_at bs 0 < 1048576 -> 8 <= Spa.u32_at bs 0 ->
Spa.u32_at bs 4 = 15 -> Spa.u32_at bs 8 = 262146 ->
Spa.is_object_type bs Model.POD_OBJECT_PROPS = true.
Proof.
intros bs H1 H2 H3 H4. rewrite hgh_obj_eq.
rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Z.leb_le _ _) H2),
  (proj2 (Z.eqb_eq _ _) H4). reflexivity.
Qed.

(* size < 16: the find loop's first spa_pod_prop_is_inside fails, so there is no params property *)
Lemma hgh_find_none : forall bs, (0 < length bs)%nat -> Spa.u32_at bs 0 < 16 ->
Spa.find_prop bs (Spa.u32_at bs 0) Model.POD_PROP_PARAMS 16 (length bs) = None.
Proof.
intros bs Hl H. destruct (length bs) as [|f] eqn:EL; [lia|].
cbn [Spa.find_prop]. unfold Spa.prop_is_inside, Spa.ptr_type_inside, Spa.ptrinside.
rewrite (proj2 (Z.leb_gt 16 _) H), !andb_false_r. reflexivity.
Qed.

(* ---------------------------------- the engine's forms ---------------------------------- *)
Lemma hgh_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.
Ltac hgh_io :=
let rec kio := first [apply same_io_refl | assumption | eapply same_io_trans; [| apply hgh_same_io_wvb]; kio] in kio.

(* the sign-extended 32-bit load of a word below 2 ^ 31 *)
Lemma hgh_U_sx32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia.
rewrite (Z.mod_small v (2 ^ Z.of_N 32)) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma hgh_U_sx32_mod : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
  rewrite !Z.mod_small by lia. reflexivity.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 31) (2 ^ 32)) by lia.
  replace (v - 2 ^ 31 - 2 ^ 31) with ((v - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (v - 2 ^ 32 + 2 ^ 64) (2 ^ 64)) by lia.
  replace (v - 2 ^ 32 + 2 ^ 64) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* `srliw rd,rs,20` of a sign-extended 32-bit load *)
Lemma hgh_U_srliw20 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
U E (SAluw ALU_SRL (SExt true 32 (SOff n 0)) (SLit 20)) = v / 2 ^ 20.
Proof.
intros E n v Hn Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (hgh_U_sx32_mod E n v Hn Hv), U_SLit. change (zcanon 20 mod 2 ^ 32) with 20.
change (Z.land 20 31) with 20. rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= v / 2 ^ 20 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* `bne` of a sign-extended 32-bit load against a literal below 2 ^ 31 *)
Lemma hgh_U_sx32_eqb : forall E n s c, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? U E (SLit c)) = (s =? c).
Proof.
intros E n s c Hn Hs Hc. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n s Hn) by lia.
rewrite U_lit by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
destruct (Z.ltb_spec s (2 ^ 31)).
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (s - 2 ^ 31)) by lia.
  replace (s - 2 ^ 31 - 2 ^ 31) with ((s + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (s + (2 ^ 64 - 2 ^ 32)) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.

Lemma hgh_U_add_lit : forall E a v c, U E a = v -> 0 <= v + c < 2 ^ 64 -> - 2 ^ 64 < c < 2 ^ 64 ->
U E (SAlu ALU_ADD a (SLit c)) = v + c.
Proof.
intros E a v c Ha Hv Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. unfold zcanon, M64.
rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia.
Qed.

Lemma hgh_U_add2 : forall E a b u v, U E a = u -> U E b = v -> 0 <= u + v < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = u + v.
Proof.
intros E a b u v Ha Hb Huv. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64. lia.
Qed.

Lemma hgh_u32_u64 : forall v, 0 <= v < 2 ^ 32 -> bv_unsigned (w64 v) = v.
Proof.
intros v H. apply unsigned_lit_small.
change (2 ^ 32) with 4294967296 in H. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma hgh_sh_low {rc : YM05.RunCeil} : forall a, 0 <= a < 2 ^ 47 -> 0 <= shadow_addr a < alloc_ceiling.
Proof.
intros a Ha. pose proof ASAN_CEIL_range as [[A1 A2] _]. unfold ASAN_CEIL in A1.
assert (Hd : a / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
assert (Hd0 : 0 <= a / 8) by (apply Z.div_pos; lia).
change (2 ^ 47 / 8) with 17592186044416 in Hd.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma hgh_le_byte_0 : forall n k, YO0f.le_byte 0 n k = 0.
Proof. intros n k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity. Qed.

(* ======================================= over segs ======================================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Context {akey aph apad asens gotw guard : Z} {dcs : list (Z * Z)}.
Local Notation call_ok := (hp_call_ok B akey aph apad asens gotw guard dcs).
Implicit Types (x : @hp_ctx segs).

(* ---------------------------------- the model at the exits of segment E ---------------------------------- *)
(* a NULL first argument: the contract's answer is parse_props None cap *)
Lemma hgh_ans_null : forall x, hx_null x = 1 -> hx_ans x = (-1, [], (0, 0, Headamp.REFUSE_NONE)).
Proof. intros x H. unfold hx_ans, hd_props. rewrite H. reflexivity. Qed.

(* a non-NULL first argument: the answer is Headamp.parse_model of the pod's bytes *)
Lemma hgh_ans_res : forall x, hx_null x = 0 -> hx_ans x = hx_res x.
Proof. intros x H. unfold hx_ans, hx_res, hd_props. rewrite H. reflexivity. Qed.

(* not a Props object *)
Lemma hgh_res_notprops : forall x,
Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = false ->
hx_res x = (-1, [], (0, 0, Headamp.REFUSE_NONE)).
Proof. intros x H. unfold hx_res, Headamp.parse_model, Spa.spa_view_of. rewrite H. reflexivity. Qed.

(* a Props object with no params property *)
Lemma hgh_res_noparams : forall x,
Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = true ->
Spa.find_prop (hx_bs x) (Spa.u32_at (hx_bs x) 0) Model.POD_PROP_PARAMS 16 (length (hx_bs x)) = None ->
hx_res x = (0, [], (0, 0, Headamp.REFUSE_NONE)).
Proof.
intros x H E. unfold hx_res, Headamp.parse_model, Spa.spa_view_of. rewrite H. cbn [negb].
rewrite E. reflexivity.
Qed.

(* size >= 16: the find loop at r = 16, with the fuel the cut asks for *)
Lemma hgh_res_find : forall x (n : nat),
Spa.is_object_type (hx_bs x) Model.POD_OBJECT_PROPS = true ->
(Z.to_nat (8 + hx_SZ x - 16) < n)%nat -> (Z.to_nat (8 + hx_SZ x - 16) < length (hx_bs x))%nat ->
hx_res x = match Spa.find_prop (hx_bs x) (hx_SZ x) Model.POD_PROP_PARAMS 16 n with
           | None => (0, [], (0, 0, Headamp.REFUSE_NONE))
           | Some r' =>
               if Spa.is_struct_at (hx_bs x) (r' + 8)
               then Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x)
                      (hp_walk_pairs (hx_bs x) r' (r' + 16) (length (hx_bs x)) None) [] 0 Headamp.REFUSE_NONE)
               else (0, [], (0, 0, Headamp.REFUSE_NONE))
           end.
Proof.
intros x n H Hn Hm. unfold hx_res, Headamp.parse_model, Spa.spa_view_of. rewrite H. cbn [negb].
unfold hx_SZ in *.
rewrite (Spa.find_prop_fuel (hx_bs x) (Spa.u32_at (hx_bs x) 0) Model.POD_PROP_PARAMS 16
  (length (hx_bs x)) n ltac:(lia) Hm Hn).
destruct (Spa.find_prop (hx_bs x) (Spa.u32_at (hx_bs x) 0) Model.POD_PROP_PARAMS 16 n) as [r'|];
  [|reflexivity].
destruct (Spa.is_struct_at (hx_bs x) (r' + 8)); reflexivity.
Qed.

(* ---------------------------------- regions at a pointer ---------------------------------- *)
(* a writable region at the pointer p held in env slot n *)
Lemma hgh_region_w : forall E m (n : nat) p lo hi,
bv_unsigned (ew E n) = p -> 0 <= p + lo -> p + hi <= 2 ^ 64 ->
(forall o, lo <= o < hi -> writable_at segs m (p + o)) ->
region_ok segs E m (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros E m n p lo hi Hn Hlo Hhi Hw. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [exact Hw | apply Forall_nil].
Qed.

(* a read-only region at the pointer p held in env slot n *)
Lemma hgh_region_ok : forall E m (n : nat) p lo hi cs,
bv_unsigned (ew E n) = p -> 0 <= p + lo -> p + hi <= 2 ^ 64 ->
Forall (YP09.chunk_ok segs E m p) cs ->
region_ok segs E m (YP09.mkRegion (Some n) lo hi 0 0 cs).
Proof.
intros E m n p lo hi cs Hn Hlo Hhi Hcs. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
Qed.

(* ---------------------------------- res ---------------------------------- *)
(* the three zero words res holds after the stores, as the twelve bytes hp_core asks for *)
Lemma hgh_res_zero : forall m a, val_mem segs m a 4 0 -> val_mem segs m (a + 4) 4 0 ->
val_mem segs m (a + 8) 4 0 -> forall i, 0 <= i < 12 -> mbyte segs m (a + i) = Some (Z_to_bv 8 0).
Proof.
intros m a H0 H4 H8 i Hi.
assert (HB : forall b k, val_mem segs m b 4 0 -> 0 <= k < 4 -> mbyte segs m (b + k) = Some (Z_to_bv 8 0)).
{ intros b k H Hk. specialize (H (Z.to_nat k) ltac:(lia)).
  replace (b + Z.of_nat (Z.to_nat k)) with (b + k) in H by lia.
  rewrite H, hgh_le_byte_0. reflexivity. }
destruct (Z_lt_le_dec i 4) as [Hl|Hl]; [apply (HB a i H0); lia|].
destruct (Z_lt_le_dec i 8) as [Hm|Hm].
- replace (a + i) with ((a + 4) + (i - 4)) by lia. apply (HB _ _ H4). lia.
- replace (a + i) with ((a + 8) + (i - 8)) by lia. apply (HB _ _ H8). lia.
Qed.

Lemma hgh_res_garr8 : forall m a, (forall i, 0 <= i < 12 -> mbyte segs m (a + i) = Some (Z_to_bv 8 0)) ->
garr8 segs m a (hd_zbytes (ha_res_bytes 0 0 0)).
Proof.
intros m a H.
assert (HL : hd_zbytes (ha_res_bytes 0 0 0) = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])
by (vm_compute; reflexivity).
assert (HN : forall j, nth j [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] 0 = 0)
by (intros j; destruct j as [|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]; [..|destruct j]; reflexivity).
rewrite HL. intros j Hj. cbn [length] in Hj. rewrite HN.
split; [|lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, hgh_le_byte_0.
apply (H (Z.of_nat j)). lia.
Qed.

(* where res lies: below 2 ^ 47, 4-aligned, apart from the hole, and so is its shadow *)
Lemma hgh_res_bounds : forall x, call_ok x -> hx_R x <> 0 ->
4 <= hx_R x /\ hx_R x + 12 <= 2 ^ 47 /\ hx_R x mod 4 = 0.
Proof.
intros x Hc HR0. pose proof (hk_res B segs_low x Hc HR0) as (Hal & _ & _ & Hb).
pose proof ASAN_CEIL_range as [[A1 A2] _].
destruct (Hb (hx_R x) ltac:(lia)) as (_ & _ & Hlo).
destruct (Hb (hx_R x + 11) ltac:(lia)) as (_ & _ & Hhi).
unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
split; [destruct Hlo as [Hd|(Hd & _)]; lia|].
split; [destruct Hhi as [Hd|(_ & [Hd|(_ & Hd)])]; lia | exact Hal].
Qed.

Lemma hgh_res_not_hole : forall x, call_ok x -> hx_R x <> 0 ->
forall a, hx_R x <= a < hx_R x + 12 -> ~ hp_hole x a.
Proof.
intros x Hc HR0 a Ha Hh. pose proof (hk_res B segs_low x Hc HR0) as (_ & _ & _ & Hb).
pose proof (hk_hole_band B x a Hc Hh) as (Hb1 & Hb2).
pose proof ASAN_CEIL_range as [[A1 A2] _].
destruct (Hb a Ha) as (_ & _ & Hd).
unfold app_addr, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF, ASAN_CEIL in *.
destruct Hd as [Hd|(_ & [Hd|(Hd & _)])]; lia.
Qed.

Lemma hgh_sh_res_not_hole : forall x, call_ok x -> hx_R x <> 0 ->
forall i, 0 <= i < 12 -> ~ hp_hole x (shadow_addr (hx_R x + i)).
Proof.
intros x Hc HR0 i Hi.
pose proof (hk_res B segs_low x Hc HR0) as (_ & _ & Hside & _).
pose proof (hk_frame_win B x Hc) as (_ & _ & _ & Hfr & _).
apply (hk_sh_not_hole B x (hx_R x + i) Hc). unfold T_parse_STK, T_PARSE_FRAME, ESTACK in Hside. lia.
Qed.

(* the view of a byte no write window of a run covers *)
Lemma hgh_view_kept : forall x (m m2 : word -> option byte) a,
m2 (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> hx_view x m2 a = hx_view x m a.
Proof. intros x m m2 a H. unfold hx_view, aview, mbyte, mrestrict. rewrite H. reflexivity. Qed.

(* ---------------------------------- hp_core from its pieces ---------------------------------- *)
Lemma hgh_core_mk : forall x cl rb regs mem md,
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem md (hx_k x) (hx_fr x) PAT_KEY ->
same_io (hx_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
 ~ hp_pw B x (Z.of_nat (length cl)) a -> hx_view x mem a = hx_view x (hx_memc x) a) ->
hp_saved_ok x mem ->
garr8 segs (hx_rd x mem) (hx_O x) (hd_zbytes (ha_cells_bytes cl)) ->
(hx_R x <> 0 -> garr8 segs (hx_rd x mem) (hx_R x) (hd_zbytes rb)) ->
(exists ev', rd32 (hx_view x mem) (as_errno B) ev') ->
hk_cregs x regs ->
hp_core B x PAT_KEY cl rb regs mem md.
Proof.
intros x cl rb regs mem md HJ Hio HK HS HO HR HE (H2 & H8 & H3 & H4 & H9 & H18 & H19 & H26 & H27).
unfold hp_core.
split; [exact HJ|]. split; [exact Hio|]. split; [exact HK|]. split; [exact HS|].
split; [exact HO|]. split; [exact HR|]. split; [exact HE|].
split; [exact H2|]. split; [exact H8|]. split; [exact H3|]. split; [exact H4|].
split; [exact H9|]. split; [exact H18|]. split; [exact H19|]. split; [exact H26 | exact H27].
Qed.

Lemma hgh_garr8_nil : forall x mem, garr8 segs (hx_rd x mem) (hx_O x) (hd_zbytes (ha_cells_bytes [])).
Proof. intros x mem j Hj. cbn in Hj. lia. Qed.

(* ---------------------------------- the pod's header words in the cut env ---------------------------------- *)
(* the u32 at 0, 4 and 8 of the pod, the cut env's slots 47, 48, 49 *)
Definition hgh_L x : list word :=
[w64 (Spa.u32_at (hx_bs x) 0); w64 (Spa.u32_at (hx_bs x) 4); w64 (Spa.u32_at (hx_bs x) 8)].

Lemma hgh_env_u32 : forall x regs j, (j < 3)%nat ->
ew (hk_env x regs (hgh_L x)) (47 + j) = w64 (Spa.u32_at (hx_bs x) (4 * Z.of_nat j)).
Proof.
intros x regs j Hj. rewrite (hk_env_seg x regs (hgh_L x) j).
destruct j as [|[|[|j]]]; cbn [nth hgh_L]; try reflexivity. lia.
Qed.

Lemma hgh_afact_u32 : forall x regs (n : nat) j, (j < 3)%nat -> n = (47 + j)%nat ->
afact_ok (hk_env x regs (hgh_L x)) n (mkAF 0 (2 ^ 32 - 1) 0).
Proof.
intros x regs n j Hj ->. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (hgh_env_u32 x regs j Hj).
pose proof (hgw_u32_range (hx_bs x) (4 * Z.of_nat j)) as Hr.
rewrite (hgh_u32_u64 _ Hr). change (2 ^ 32) with 4294967296 in Hr |- *.
rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

(* a0 = P, 16-aligned, the pod's header inside [16, 2 ^ 47) *)
Lemma hgh_afact_P : forall x regs, getr regs 10 = w64 (hx_P x) ->
16 <= hx_P x -> hx_P x + 16 <= 2 ^ 47 -> hx_P x mod 16 = 0 ->
afact_ok (hk_env x regs (hgh_L x)) 10 (mkAF 16 (2 ^ 47 - 16) 4).
Proof.
intros x regs H10 Hlo Hhi Hal. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (hk_env_reg x regs (hgh_L x) 10%nat (10%bv : bv 5) eq_refl), H10.
rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616;
  change (2 ^ 47) with 140737488355328 in Hhi; lia).
change (2 ^ 4) with 16. repeat split; lia.
Qed.

(* ---------------------------------- the first cut after the open: what the call gives ---------------------------------- *)
(* the errno cell is readable at a state that keeps every byte outside the parse's stack window and the hole: it is
   readable at the call and lies below kLowMemEnd *)
Lemma hgh_errno_kept : forall x mem, api_env segs B -> call_ok x ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
 hx_view x mem a = hx_view x (hx_memc x) a) ->
exists ev', rd32 (hx_view x mem) (as_errno B) ev'.
Proof.
intros x mem Henv Hc HK.
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Herr & _).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof Henv as [[He0 He1] [Heimg _]].
exists (hx_ev x). intros kk Hkk.
rewrite (HK (as_errno B + Z.of_nat kk)); [exact (Herr kk Hkk) | unfold kLowMemEnd in *; lia | |].
- intros Hw. pose proof (hk_window_band B x _ Hc Hw). unfold kLowMemEnd in *. lia.
- intros Hh. pose proof (hk_hole_band B x _ Hc Hh) as HB. unfold kLowMemEnd, SHADOW_OFF in *. lia.
Qed.

(* res's bytes are present at a state with the caller's journal in cut-state form and the caller's stack window
   present: res lies in that window or in a frame of the side stack for frames, which the hole does not cover *)
Lemma hgh_res_present : forall x pat mem md, call_ok x ->
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem md (hx_k x) (hx_fr x) pat ->
(forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem a) ->
hx_R x <> 0 -> forall a, hx_R x <= a < hx_R x + 12 -> apresent (w_H (hx_W x)) mem a.
Proof.
intros x pat mem md Hc HJ Hpres HR0 a Ha.
pose proof HJ as (HAJ & OK & _).
pose proof (hk_frame_win B x Hc) as HFW. pose proof (hk_stack B x Hc) as HS.
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & HR & _).
destruct HR as [HR|((Hloc & _) & _ & _)]; [contradiction|].
destruct Hloc as [Hst | (cid & pos & Hin & _ & Hf1 & Hf2)].
- apply Hpres. lia.
- assert (HinF : In (cid, pos) (frames (hx_Sc x))).
  { pose proof (hk_call_journal B x Hc) as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. apply in_or_app. left. exact Hin. }
  destruct (al_frames _ _ (AR_laws_ok segs B) _ _ _ _ _ cid pos (proj1 HAJ) HinF) as (_ & Happ & Hb & _).
  destruct (Hb a ltac:(lia)) as [Hpr _].
  assert (HIN : in_ush (hU (hx_fr x) pat) (bv_unsigned (Z_to_bv 64 a)) = false).
  { apply in_hU_false.
    rewrite unsigned_lit_small by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
    destruct OK as (_ & _ & _ & Hhi & _).
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
  exact (proj1 (hp_apresent_unp (w_H (hx_W x)) (hU (hx_fr x) pat) mem a HIN) Hpr).
Qed.

End g.
