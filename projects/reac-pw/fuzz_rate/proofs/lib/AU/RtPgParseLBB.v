(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseLB.v at afaa3cb55c1d; module paths, file
   and plain-lemma names, pcs and comments changed to reac-pw/fuzz_rate's reac_rate_prop_parse on image A; the back
   edge is rate's 0x84728 beqz -> L2 (the taken side is the path to L2, the j side is refuted); lb_same_io_wvb
   replaced by RtPgParseBase.v's same_io_wvb. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgParseLB.v at f7246d55e8c3 for image B
   (fuzz_rate.asan-ubsan); image B's pcs and code; the last body byte's address is in a0 (atom 10) and P + c + 8 in a1
   (atom 11); the key select is branchless (snez / addi / and, lb_mask_U and lb_key_val, by cases on the byte), so the
   walk splits only at the alignment branch; the key slot at L2 is in a1; lib/AU/RtPgParseBaseB.v and lib/AU/Img0.v
   in place of image A's base and image. *)
(* reac_rate_prop_parse's walk on reac-pw/fuzz_rate's ASan image B, segment LB: from the cut LB 0x849a8 (the String
   child's last body byte) to the foreach head L2 0x8491c at the next child, the key slot holding the child or not. *)
(* fuzz_rate.asan-ubsan, pinned sha256 c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14 (unstripped
   twin a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, the same loaded bytes). P is the pod, c the
   child, CS = u32 at c (its size), s1 = P + c; LB_at gives a0 = P + c + 8 + CS - 1, a1 = P + c + 8 and
   s8 = ((P + c) >> 3) + SHADOW_OFF. The code:
     0x849a8 .. 0x849b4  the instrumented 1-byte check of a0 (shadow entry mkSHE 10 0 1; its slow path 0x84a48 andi
                         a3,a0,7 + 0x84a4c blt a3,a2 -> 0x849b8, and the error call 0x84a50 there, are refuted by the
                         engine from that entry);
     0x849b8 lbu a0,0(a0) (the last body byte b); 0x849bc snez a0,a0; 0x849c0 addi a0,a0,-1; 0x849c4 and a1,a0,a1:
                         the mask is 2^64 - 1 when b = 0 and 0 else, so a1 = P + c + 8 when b = 0 (the child is the
                         pending key) and a1 = 0 else (no key); no branch: the engine keeps a1 as one value, and
                         lb_key_val gives it by cases on b (atom 43, mkAF 0 255 0); 0x849c8 j 0x849e0;
     0x849e0 lb a0,0(s8); 0x849e4 bnez: the check of s1 (shadow entry mkSHE 9 0 4; slow path 0x84a18 .. 0x84a24);
     0x849e8 lwu a0,0(s1); addi 7; ori 7; add s1; 0x849f8 addi s1,a0,1: s1 = P + c + ((CS + 7) | 7) + 1 = P + c',
                         c' = c + round_up8 (8 + CS) (lb_U_s1);
     0x849fc andi a0,s1,3; 0x84a00 beqz a0: TAKEN to 0x8491c (L2), c' mod 4 = 0 (lb_aligned); not taken
                         0x84a04 j 0x84804 (li a0,0; j 0x84ba4: ret 0): refuted.
   LB has no trap branch: the String path's two branches to the `unimp` 0x84bd4 (0x84994 bltu, 0x849a4 beqz) are
   before the cut, in segment L.
   The entry env is cut_env x regs2 [b; CS] (atoms 43, 44); register s8 is the expression the engine forms for
   0x84930 srli s8,s1,3 / 0x84934 add s8,s8,s3 (lb_s8). The two pod reads are read-only regions at atoms 10 ([0, 1),
   chunk atom 43) and 9 ([0, 4), chunk atom 44); no byte is written, so the memory at L2 is the memory at LB. The
   model: walk_res_step at a child inside the Struct with the key slot empty gives the walk at c' with the slot
   spa_get_string (child_at bs c) (lb_walk), and that is Some exactly when b = 0, the size and type tests holding at
   LB (lb_gs, from the plain walk's pb_gs). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require reac_rate_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0 RtPgParseBaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------- the entry state ---------------------------------- *)
(* 0x84930 srli s8,s1,3; 0x84934 add s8,s8,s3 with s1 = atom 9, s3 = atom 19 (the engine's form) *)
Definition lb_s8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0).
Definition lb_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 43 0))];
  YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 44 0))] ].
(* s1 = P + c and a0 = P + c + 8 + CS - 1 lie below 2^47 (the pod's amem_range), s3 = SHADOW_OFF, the byte and the
   size word *)
Definition lb_facts : facts :=
mkFacts [ (9%nat, mkAF 0 (2 ^ 47 - 4) 2); (10%nat, mkAF 0 (2 ^ 47 - 1) 0); (19%nat, mkAF SBr SBr 0);
          (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 (2 ^ 32 - 1) 0) ] [] [].
Definition ss_lb : sstate := mkSS PC_LB (sr_set sr_atoms 24%bv lb_s8) lb_regions None lb_facts.
Definition lb_SH : list shent := [mkSHE 10 0 1; mkSHE 9 0 4].
(* the registers the segment leaves as they were at LB *)
Definition lb_kept : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.

(* the last body byte b of the child at c, and the env cut_env x regs2 [b; CS] as an Ereg *)
Definition lb_b (x : pctx) (c : Z) : Z := nth (Z.to_nat (c + 8 + Spa.u32_at (x_bs x) c - 1)) (bvals (x_bs x)) 0.
Definition lb_L (x : pctx) (c : Z) : list word := [Z_to_bv 64 (lb_b x c); Z_to_bv 64 (Spa.u32_at (x_bs x) c)].
Definition lb_extra (x : pctx) (c : Z) : list word := w64 SBr :: saved_vals (x_regs x) ++ lb_L x c.

(* ---------------------------------- the values ---------------------------------- *)
(* 0x849e8 .. 0x849f8: s1 + ((CS + 7) | 7) + 1 = s1 + round_up8 (8 + CS) *)
Lemma lb_U_s1 : forall E p cs, ew E 9 = Z_to_bv 64 p -> ew E 44 = Z_to_bv 64 cs ->
0 <= p -> 0 <= cs < 2 ^ 32 -> p + Spa.round_up8 (8 + cs) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 44 7) (SLit 7))) (SLit 1)) = p + Spa.round_up8 (8 + cs).
Proof.
intros E p cs H9 H44 Hp Hcs Hlt.
pose proof (reac_rate_prop_parse.pb_lor7 cs ltac:(lia)) as (L1 & L2 & _).
rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 9 p H9) by lia. rewrite (U_atom_off E 44 cs 7 H44) by lia.
cbn [zalu_raw].
rewrite (zcanon_id 7) by (unfold M64; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite (zcanon_id (Z.lor (cs + 7) 7)) by (unfold M64; lia).
rewrite (zcanon_id (p + Z.lor (cs + 7) 7)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma lb_s1_val : forall E p cs, ew E 9 = Z_to_bv 64 p -> ew E 44 = Z_to_bv 64 cs ->
0 <= p -> 0 <= cs < 2 ^ 32 -> p + Spa.round_up8 (8 + cs) < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 44 7) (SLit 7))) (SLit 1)) =
w64 (p + Spa.round_up8 (8 + cs)).
Proof. intros E p cs H9 H44 Hp Hcs Hlt. rewrite denot_lit_U, (lb_U_s1 E p cs H9 H44 Hp Hcs Hlt). reflexivity. Qed.

(* 0x849fc andi a0,s1,3: 0 *)
Lemma lb_aligned : forall E p cs, ew E 9 = Z_to_bv 64 p -> ew E 44 = Z_to_bv 64 cs ->
0 <= p -> p mod 4 = 0 -> 0 <= cs < 2 ^ 32 -> p + Spa.round_up8 (8 + cs) < 2 ^ 64 ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 44 7) (SLit 7))) (SLit 1)) (SLit 3)) = 0.
Proof.
intros E p cs H9 H44 Hp H4 Hcs Hlt.
rewrite U_and_lit by lia. rewrite (lb_U_s1 E p cs H9 H44 Hp Hcs Hlt).
pose proof (reac_rate_prop_parse.pb_lor7 cs ltac:(lia)) as (_ & L2 & L3).
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
rewrite <- L2. lia.
Qed.

(* the s8 of LB_at is lb_s8's value *)
Lemma lb_s8_val : forall E p, ew E 9 = Z_to_bv 64 p -> ew E 19 = Z_to_bv 64 SHADOW_OFF -> 0 <= p < 2 ^ 47 ->
sv_denot E lb_s8 = w64 (Z.shiftr p 3 + SHADOW_OFF).
Proof.
intros E p H9 H19 Hp. rewrite denot_lit_U. unfold w64. f_equal. unfold lb_s8.
rewrite !U_SAlu, U_SLit. rewrite (U_atom E 9 p H9) by lia. rewrite (U_atom E 19 SHADOW_OFF H19) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
assert (Hs : 0 <= Z.shiftr p 3 <= p) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite (zcanon_id (Z.shiftr p 3)) by (unfold M64; lia).
apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* 0x849bc snez a0,a0; 0x849c0 addi a0,a0,-1 with a0 = the byte b (atom 43): the mask, 2^64 - 1 when b = 0, else 0 *)
Definition lb_mask : sv := SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 43 0)) (SLit (-1)).
Lemma lb_mask_U : forall E b, ew E 43 = Z_to_bv 64 b -> 0 <= b < 256 ->
U E lb_mask = if b =? 0 then 2 ^ 64 - 1 else 0.
Proof.
intros E b H43 Hb. unfold lb_mask. rewrite !U_SAlu, !U_SLit. rewrite (U_atom E 43 b H43) by lia.
cbn [zalu_raw]. rewrite (zcanon_id 0) by (unfold M64; lia).
destruct (Z.eqb_spec b 0) as [-> | Hn].
- vm_compute. reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 b)) by lia. vm_compute. reflexivity.
Qed.

(* 0x849c4 and a1,a0,a1 with a1 = P + c + 8 (atom 11): the key slot, P + c + 8 when b = 0, else 0 *)
Lemma lb_key_val : forall E b k, ew E 43 = Z_to_bv 64 b -> ew E 11 = Z_to_bv 64 k -> 0 <= b < 256 ->
0 <= k < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND lb_mask (SOff 11 0)) = w64 (if b =? 0 then k else 0).
Proof.
intros E b k H43 H11 Hb Hk. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, (lb_mask_U E b H43 Hb), (U_atom E 11 k H11 Hk). cbn [zalu_raw].
destruct (b =? 0).
- replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.land_comm, Z.land_ones by lia.
  rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
- rewrite Z.land_0_l. reflexivity.
Qed.

(* ---------------------------------- the model ---------------------------------- *)
Lemma bvals_nth : forall l n, nth n (bvals l) 0 = bv_unsigned (nth n l Cursor.NUL).
Proof.
intros l n. unfold bvals.
transitivity (nth n (map (fun b : byte => bv_unsigned b) l) ((fun b : byte => bv_unsigned b) Cursor.NUL));
[reflexivity | apply map_nth].
Qed.

(* spa_pod_get_string of the child at c when the size and type tests hold: Some exactly when the last body byte is 0 *)
Lemma lb_gs : forall bs c, 0 <= c -> c + 8 + Spa.u32_at bs c <= Z.of_nat (length bs) ->
1 <= Spa.u32_at bs c < Spa.SPA_POD_MAX_SIZE -> Spa.u32_at bs (c + 4) = Model.POD_STRING ->
Spa.spa_get_string (Spa.child_at bs c) =
if nth (Z.to_nat (c + 8 + Spa.u32_at bs c - 1)) (bvals bs) 0 =? 0
then Some (Cursor.cstr (firstn (Z.to_nat (Spa.u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs))) else None.
Proof.
intros bs c H0 H1 H2 H3. rewrite (reac_rate_prop_parse.pb_gs bs c H0 H1).
unfold Spa.SPA_POD_MAX_SIZE in H2.
rewrite (proj2 (Z.ltb_lt (Spa.u32_at bs c) (2 ^ 20))) by lia.
rewrite (proj2 (Z.leb_le 1 (Spa.u32_at bs c))) by lia.
rewrite H3. change (Model.POD_STRING =? 8) with true. cbn [andb].
rewrite bvals_nth. reflexivity.
Qed.

(* one pass of the foreach at a child inside the Struct with the key slot empty *)
Lemma lb_walk : forall bs r c, 0 <= c ->
Spa.pod_is_inside bs (r + 16) (Spa.u32_at bs (r + 8)) c = true ->
walk_res bs (r + 16) (Spa.u32_at bs (r + 8)) c (S (Z.to_nat (r + 16 + Spa.u32_at bs (r + 8) - c))) None =
walk_res bs (r + 16) (Spa.u32_at bs (r + 8)) (c + Spa.round_up8 (8 + Spa.u32_at bs c))
  (S (Z.to_nat (r + 16 + Spa.u32_at bs (r + 8) - (c + Spa.round_up8 (8 + Spa.u32_at bs c)))))
  (Spa.spa_get_string (Spa.child_at bs c)).
Proof.
intros bs r c Hc0 Hin.
pose proof Hin as Hin'.
unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining in Hin'.
rewrite !andb_true_iff, !Z.leb_le in Hin'.
destruct Hin' as [[_ [[H1 H2] H3]] H4].
pose proof (u32_at_range bs c) as Hcs.
pose proof (reac_rate_prop_parse.pb_lor7 (Spa.u32_at bs c) ltac:(lia)) as (L1 & L2 & _).
rewrite reac_rate_prop_parse.walk_res_step, Hin.
unfold reac_rate_prop_parse.walk_res.
rewrite (Spa.struct_children_fuel bs (r + 16) (Spa.u32_at bs (r + 8)) (c + Spa.round_up8 (8 + Spa.u32_at bs c))
  (Z.to_nat (r + 16 + Spa.u32_at bs (r + 8) - c))
  (S (Z.to_nat (r + 16 + Spa.u32_at bs (r + 8) - (c + Spa.round_up8 (8 + Spa.u32_at bs c)))))); [reflexivity | lia | lia | lia].
Qed.

(* membership of a register literal in lb_kept *)
Ltac inlit := cbn [In]; repeat first [left; first [reflexivity | apply bv_eq; reflexivity] | right].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.

(* the bounds LB_at gives *)
Lemma lb_nums : forall x r c, pre_ok B x -> struct_ok x r -> child_in x r c ->
0 < x_P x /\ x_P x mod 16 = 0 /\ x_P x + x_len x < 2 ^ 47 /\ 16 <= r /\
r + 16 <= c /\ 8 <= Spa.u32_at (x_bs x) (r + 8) /\
c + 8 + Spa.u32_at (x_bs x) c <= r + 16 + Spa.u32_at (x_bs x) (r + 8) /\
r + 16 + Spa.u32_at (x_bs x) (r + 8) <= x_len x /\ c mod 4 = 0 /\
0 <= Spa.u32_at (x_bs x) c < 2 ^ 32.
Proof.
intros x r c Hpre Hso Hin.
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & _ & _ & _ & _ & _ & HAM & _).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof asan_consts as (_ & _ & _ & C4 & _). rewrite C4 in Hhm.
destruct Hso as (Hr16 & Hr4 & _ & HVS8 & HVSl).
unfold child_in, Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining in Hin.
rewrite !andb_true_iff, !Z.leb_le, Z.eqb_eq in Hin.
destruct Hin as [[Hc4 [[H1 H2] H3]] H4].
pose proof (u32_at_range (x_bs x) c).
repeat split; lia.
Qed.

(* the entry state at LB and its shadow entries *)
Lemma lb_entry : forall x r c regs2 mem2 md2, pre_ok B x -> LB_at B x r c regs2 mem2 md2 ->
st_ok rsegs (Ereg regs2 (lb_extra x c)) ss_lb
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_LB) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx lb_SH (Ereg regs2 (lb_extra x c)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r c regs2 mem2 md2 Hpre HLB.
pose proof HLB as (HFI & (H9 & _) & H24 & H11 & H10 & Hso & Hc16 & Hc4 & Hin & HCS & HTY & Hres).
pose proof HFI as (_ & _ & _ & _ & _ & _ & _ & H19).
pose proof (lb_nums x r c Hpre Hso Hin) as (HP0 & HP16 & HP47 & Hr16 & Hrc & HVS8 & Hcsz & HVSl & _ & HCSr).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & _ & _).
pose proof (pod_u8 x (mrestrict (w_H (x_W x)) mem2) (c + 8 + Spa.u32_at (x_bs x) c - 1) HG ltac:(lia) ltac:(lia))
  as [Vb Bb].
fold (lb_b x c) in Vb, Bb.
pose proof (pod_u32 x (mrestrict (w_H (x_W x)) mem2) c HG ltac:(lia) ltac:(lia)) as Vcs.
assert (E9 : ew (Ereg regs2 (lb_extra x c)) 9 = Z_to_bv 64 (x_P x + c))
by exact (eq_trans (ew_Ereg_nat regs2 _ 9 9%bv eq_refl) H9).
assert (E10 : ew (Ereg regs2 (lb_extra x c)) 10 = Z_to_bv 64 (x_P x + c + 8 + Spa.u32_at (x_bs x) c - 1))
by exact (eq_trans (ew_Ereg_nat regs2 _ 10 10%bv eq_refl) H10).
assert (E19 : ew (Ereg regs2 (lb_extra x c)) 19 = Z_to_bv 64 SHADOW_OFF)
by exact (eq_trans (ew_Ereg_nat regs2 _ 19 19%bv eq_refl) H19).
assert (E43 : ew (Ereg regs2 (lb_extra x c)) 43 = Z_to_bv 64 (lb_b x c)) by exact (cut_env_seg x regs2 (lb_L x c) 0).
assert (E44 : ew (Ereg regs2 (lb_extra x c)) 44 = Z_to_bv 64 (Spa.u32_at (x_bs x) c))
by exact (cut_env_seg x regs2 (lb_L x c) 1).
assert (U19 : U (Ereg regs2 (lb_extra x c)) PBx = SHADOW_OFF) by (apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]).
split.
- rewrite restrict_mkst_fx. unfold ss_lb. apply (entry_st_ok_full rsegs).
  + apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |].
    rewrite H24. unfold s8_val. symmetry. apply lb_s8_val; [exact E9 | exact E19 | lia].
  + vm_compute. reflexivity.
  + unfold lb_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E10, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 43 0) (lb_b x c)); [rewrite sv_denot_SOff0; exact E43 | zside | zside |].
      rewrite Z.add_0_r. replace (x_P x + c + 8 + Spa.u32_at (x_bs x) c - 1) with (x_P x + (c + 8 + Spa.u32_at (x_bs x) c - 1)) by lia.
      exact Vb.
    * rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 44 0) (Spa.u32_at (x_bs x) c)); [rewrite sv_denot_SOff0; exact E44 | zside | zside |].
      rewrite Z.add_0_r. exact Vcs.
  + apply pairwise_disjoint_of_extents. unfold lb_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E10, E9, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | exact I]]. cbn [lb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E10, E19, E43, E44, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    unfold SBr, SHADOW_OFF. repeat split; lia.
- unfold sh_ok, lb_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_pod B x regs2 mem2 md2 _ PBx 10 (c + 8 + Spa.u32_at (x_bs x) c - 1) 0 1 Hpre HFI U19); [| lia | lia | lia].
    rewrite (U_atom _ 10 _ E10) by lia. lia.
  + apply (shent_pod B x regs2 mem2 md2 _ PBx 9 c 0 4 Hpre HFI U19); [| lia | lia | lia].
    rewrite (U_atom _ 9 _ E9) by lia. reflexivity.
Qed.


(* the foreach head L2 at c' = c + round_up8 (8 + CS), the key slot Some c exactly when the last body byte is 0 *)
Lemma lb_exit : forall x r c regs2 mem2 md2 regs3 md3 (ko : option Z),
pre_ok B x -> LB_at B x r c regs2 mem2 md2 ->
(forall c' ko', c < c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok B MT x r c' ko') ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
  (x_lyc x) (x_Sc x) (x_W x) mem2 md3 (x_k x) ->
same_io md2 md3 ->
(forall rr, In rr lb_kept -> getr regs3 rr = getr regs2 rr) ->
getr regs3 9 = w64 (x_P x + c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) ->
getr regs3 11 = w64 (match ko with None => 0 | Some ck => x_P x + ck + 8 end) ->
ko = (if lb_b x c =? 0 then Some c else None) ->
SRr rsegs (x_W x) (cfg_at rsegs PC_L2 regs3 mem2 md3) (PPOST B MT x false).
Proof.
intros x r c regs2 mem2 md2 regs3 md3 ko Hpre HLB HL2 HJ3 Hio3 HR H9' H11' Hko.
pose proof HLB as (HFI & (H9 & H18 & H20 & H21 & H22 & H23) & H24 & H11 & H10 & Hso & Hc16 & Hc4 & Hin & HCS & HTY & Hres).
pose proof HFI as (HJ & Hio & HK & HSV & H2 & Hcs & H8 & H19).
pose proof (lb_nums x r c Hpre Hso Hin) as (HP0 & HP16 & HP47 & Hr16 & Hrc & HVS8 & Hcsz & HVSl & _ & HCSr).
pose proof (reac_rate_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (L1 & L2 & L3).
assert (HRk : forall rr : bv 5, In rr lb_kept -> getr regs3 rr = getr regs2 rr) by exact HR.
assert (Hlen : c + 8 + Spa.u32_at (x_bs x) c <= Z.of_nat (length (x_bs x))) by (unfold x_len in HVSl; lia).
apply (HL2 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) ko); [lia|].
unfold L2_at. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- (* FI *)
  split; [exact HJ3|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact HK|]. split; [exact HSV|].
  split; [rewrite (HRk 2%bv) by inlit; exact H2|].
  split.
  + intros rr Hrr. pose proof (Hcs rr Hrr) as Hc.
    destruct Hrr as [-> | [-> | [-> | [-> | ->]]]]; (rewrite HRk by inlit); exact Hc.
  + split; [rewrite (HRk 8%bv) by inlit; exact H8 | rewrite (HRk 19%bv) by inlit; exact H19].
- (* l2_regs at c' *)
  unfold l2_regs.
  split; [rewrite H9'; unfold w64; f_equal; lia|].
  split; [rewrite (HRk 18%bv) by inlit; exact H18|].
  split; [rewrite (HRk 20%bv) by inlit; exact H20|].
  split; [rewrite (HRk 21%bv) by inlit; exact H21|].
  split; [rewrite (HRk 22%bv) by inlit; exact H22 | rewrite (HRk 23%bv) by inlit; exact H23].
- exact H11'.
- exact Hso.
- lia.
- lia.
- (* the pending key *)
  intros ck Hck. subst ko. destruct (lb_b x c =? 0) eqn:Eb; [|discriminate Hck].
  injection Hck as <-. unfold key_ok. split; [lia|]. split; [lia|].
  rewrite (lb_gs (x_bs x) c ltac:(lia) Hlen HCS HTY). unfold lb_b in Eb. rewrite Eb. discriminate.
- (* the model *)
  rewrite Hres. unfold l2_fuel. rewrite (lb_walk (x_bs x) r c ltac:(lia) Hin).
  subst ko. destruct (lb_b x c =? 0) eqn:Eb; cbn [l2_key]; [reflexivity|].
  rewrite (lb_gs (x_bs x) c ltac:(lia) Hlen HCS HTY). unfold lb_b in Eb. rewrite Eb. reflexivity.
Qed.

(* the memory after a run over the read-only regions: the memory before it *)
Ltac lb_mem HM :=
match goal with HF : frame_of ?E ?rs ?m (ms_mem ?msb) |- _ =>
let H := fresh "HMn" in
pose proof (frame_of_read_only E rs m (ms_mem msb) ltac:(vm_compute; reflexivity) HF) as H;
first [rewrite HM in H; clear HM | idtac]; rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac lb_run :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok parse_tbl_ok HS HJ SHOK RTBspan PC_L2; [awr_ok_tac | ] end.
Ltac lb_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ => srr_branch_tok parse_tbl_ok HS SHOK RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

Theorem segLB_ok : segLB_stmt B MT.
Proof using LAWS.
unfold segLB_stmt, LB_ok.
intros x r c Hpre HL2 regs2 mem2 md2 HLB.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
destruct (lb_entry x r c regs2 mem2 md2 Hpre HLB) as [HS SHOK].
pose proof HLB as (HFI & (H9 & _) & H24 & H11 & H10 & Hso & Hc16 & Hc4 & Hin & HCS & HTY & Hres).
pose proof HFI as (HJ & Hio & _ & _ & _ & _ & _ & H19).
pose proof (lb_nums x r c Hpre Hso Hin) as (HP0 & HP16 & HP47 & Hr16 & Hrc & HVS8 & Hcsz & HVSl & _ & HCSr).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & _ & _).
pose proof (pod_u8 x (mrestrict (w_H (x_W x)) mem2) (c + 8 + Spa.u32_at (x_bs x) c - 1) HG ltac:(lia) ltac:(lia))
  as [_ Bb].
pose proof (reac_rate_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (L1 & L2 & L3).
fold (lb_b x c) in Bb.
remember (Ereg regs2 (lb_extra x c)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (lb_extra x c)) E) by (subst E; apply env_agree_refl).
assert (E9 : ew E 9 = Z_to_bv 64 (x_P x + c)) by (subst E; exact (eq_trans (ew_Ereg_nat regs2 _ 9 9%bv eq_refl) H9)).
assert (E11 : ew E 11 = Z_to_bv 64 (x_P x + c + 8)) by (subst E; exact (eq_trans (ew_Ereg_nat regs2 _ 11 11%bv eq_refl) H11)).
assert (E43 : ew E 43 = Z_to_bv 64 (lb_b x c)) by (subst E; exact (cut_env_seg x regs2 (lb_L x c) 0)).
assert (E44 : ew E 44 = Z_to_bv 64 (Spa.u32_at (x_bs x) c)) by (subst E; exact (cut_env_seg x regs2 (lb_L x c) 1)).
clear HE.
assert (Hlt : x_P x + c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c) < 2 ^ 64) by lia.
assert (HPc : (x_P x + c) mod 4 = 0) by lia.
unfold cfg_at. change (w64 PC_LB) with (Z_to_bv 64 PC_LB).
(* 0x849a8 .. 0x849b4 the check of the last body byte, 0x849b8 lbu, 0x849bc .. 0x849c4 the key select (no branch),
   0x849c8 j 0x849e0, 0x849e0 .. 0x849e4 the check of s1, 0x849e8 .. 0x849fc; stop at 0x84a00 beqz (alignment) *)
lb_run. lb_mem HM.
lb_branch Ha.
- (* TAKEN: c' mod 4 = 0; 0x84a00 beqz a0 -> 0x8491c: L2, the key slot Some c when b = 0, else None *)
  lb_run. lb_mem HM.
  lazymatch goal with HS : st_ok _ ?E3 ?ss3 (restrict _ ?ms3) |- SRr _ _ (mkCfg _ ?md3) _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) E3 ss3 ms3 HS eq_refl); cbn [ss_pc]; rewrite HM;
    rewrite HM in HJ;
    change (SRr rsegs (x_W x) (cfg_at rsegs PC_L2 (ms_regs ms3) mem2 md3) (PPOST B MT x false));
    apply (lb_exit x r c regs2 mem2 md2 (ms_regs ms3) md3 (if lb_b x c =? 0 then Some c else None)
             Hpre HLB HL2 HJ);
    [ let rec kio := first [exact Hio | apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio
    | intros rr Hrr;
      exact (regs_kept_of_st_ok rsegs E3 ss3 (restrict (w_H (x_W x)) ms3) regs2 (lb_extra x c) lb_kept HS
               ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) rr Hrr)
    | rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E3 ss3 ms3 9%bv HS);
      lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
      apply lb_s1_val; [exact E9 | exact E44 | lia | lia | exact Hlt]
    | rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E3 ss3 ms3 11%bv HS);
      lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
      transitivity (w64 (if lb_b x c =? 0 then x_P x + c + 8 else 0));
      [ apply lb_key_val; [exact E43 | exact E11 | lia | lia]
      | destruct (lb_b x c =? 0); reflexivity ]
    | reflexivity ]
  end.
- (* not taken, 0x84a04 j 0x84804 (ret 0): refuted, c' mod 4 = 0 *)
  exfalso. rewrite branch_eq_U in Ha.
  erewrite (lb_aligned _ (x_P x + c) (Spa.u32_at (x_bs x) c)) in Ha; [| exact E9 | exact E44 | lia | exact HPc | lia | exact Hlt].
  rewrite U_lit in Ha by lia. discriminate Ha.
Qed.
End b.

Print Assumptions segLB_ok.
