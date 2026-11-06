(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: ex_ws (fuzz_preset.c :103-107) of fuzz_preset's asan-ubsan image B' (#102 pin d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), out of line in B only (image A inlines it into check_as_written and ex_value),
   proved against the #102 text tex_ws_specX (lib/A/PRH_FnEx.v 45ddb7a7d5ae, PRH_Base.v 3004a98fe2d9, both = the kit of
   record decff67d721f) at the image-B' instance:
   listing B_prog_listing / PI_prog_B (the B' whole-range listing, lib/B/Listing_prog.v c97cc46b3e13 / PAImg_prog.v
   15fab93fe702; the walk runs over the instance's table pa_tbl = B_prog_tbl), frame table prh_img_B (lib/B/PRH_ImgB.v),
   journal YCbqG's ajournal_x (c3b5d0111037, engine set of record 8a01e111a410;
   table runners SRr_run_tok_AJx / SRr_run_to_tok_AJx), entry journal by YCbqGcallW's ajournal_x_init_W (same engine).
   Donor: the old-pin proof of this file (cold/h-rw-pre-7-b-ex_ws-core 097fba0abfcc, blob bdcc5f65edce).
   - THE m-FORM POST (fpostWm = fpostW at fQmn mem Q, PRH_Base.v): the keep `memnorm segs mem -> memnorm segs mem'`
     (YAkMemnorm 96c72061b4d4). The walk (Section m) carries a memory invariant Pinv with YC80x's srr_inv_laws
     (YC80x 14f84f225e8f): exw_chain_inv / exw_run_inv / exw_run_to_inv below are YCbqG's SRr_chain_tok_AJx /
     SRr_run_tok_AJx / SRr_run_to_tok_AJx with YA0n.SRr_msteps replaced by YC80x.SRr_msteps_inv; a branch
     (SRr_sym_branch) and the return (SRr_ret_at) keep the memory. ex_ws_holds_x takes Pinv := the keep from the entry
     memory, whose laws are YSRrMemnorm.srr_inv_laws_imp over srr_inv_laws_memnorm_k (YSRrMemnorm 5ffa8525936b).
     ex_ws makes no call but the ASan report stubs (B' listing slots 2794-2848: PCall __asan_report_load1 / _store8 /
     _load8 only), so no callee keep is needed, and S' = S (the walk's witness is the entry S).
   - RELOCATE ONLY. ex_ws at B' 0x84274 (220 bytes, 55 words) against old B 0x83ffc (f8f98a95 / twin 3b5e1a09):
     the instruction words are equal up to pc-relative fields (5 pc-relative, 0 real, 0 unmeasured),
     target-differ 0: all 18 pc-relative words name the same symbol + offset (the GOT word A_OBJ 0 holds
     &__asan_shadow_memory_dynamic_address = A_OBJ 12 in both; the three calls are the ASan report stubs); its one lui
     is the raw constant 0x800013, the whitespace mask, not an address. 2026-10-30.
   - THE BODY. ex_ws (B_prog_sigma AS_ex_ws, 55 instructions) is skip_ws (B_prog_sigma AS_skip_ws) instruction for
     instruction once the pc-relative fields are masked (the internal file neutral_dis.py on the old pins f8f98a95 / 3b5e1a09, 2026-10-28). The
     segment lemmas below are therefore h-verbs-1's skip_ws walk (lib/B/Prog/skip_ws_x.v, origin/cold/
     h-verbs-1-preset-leaf-skip_ws 2f4e237337f) re-pointed at ex_ws's entry, at the whole-range table and at the
     image facts of this file's Section; its q bound is the stack's (q + 16 <= 2 ^ 47) instead of amem_range.
   - THE THREE UBSan CHECKS (all trap to `unimp`, the internal file B-U-TRAPS.md, measured on the old pins) are resolved
     NOT TAKEN inside the symbolic runs from the run's facts: entry + 0xc `bnez (q & 7)` by q mod 8 = 0 (fact on q,
     alignment 3), entry + 0x64 `beqz p` by 4096 <= p (fact on the text pointer), entry + 0x90 `bgeu 1, p + 1` by
     p + 1 <= 2 ^ 47 (fact bound). The four ASan checks (q, q + 8, *p, the store to q) are resolved by the shadow
     hints (shent) from range_addressable on [q, q + 16) and on the text.
   - WHERE q's SHADOW COMES FROM. The text puts q on the real stack above the entry sp (spZ <= q, q + 16 <= spZ + d);
     its zero shadow is AR_laws_x's per-byte stack law alx_zshadow_byte (YCbqG c3b5d0111037), not the range form
     alx_zshadow, which needs 8-aligned stack bounds that ARx does not give.
   Numerals: 16 (LENGTH: ex_ws's frame, `addi sp, sp, -16`); 100 (LENGTH: offset of the loop head, entry + 0x64);
   4294977024 (WORD: the bit set lui 0x800 / addiw 19 / slli 9 builds = {9, 10, 13, 32}, PjGrammar.ws's characters);
   0x7fff8000 (DERIVED: SHADOW_OFF); 32 (WORD: the `li a6, 32` bound); 1 (WORD: `li t0, 1`); 8, 3, 4, 2 ^ 46,
   2 ^ 47, 4096, 2 ^ 63, 2 ^ 64, 2 ^ 32, 255 (LENGTH / DERIVED: widths, alignments, address-space bounds).
   No ADDRESS: entry, loop head, GOT word and shadow cell are B_prog_sigma / B_prog_val terms. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC80x YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image numbers, all from the generated listing ---- *)
Definition EXW_TSTK : Z := 16.
Definition EXW_PC : Z := B_prog_sigma AS_ex_ws.
Definition EXW_LOOP : Z := EXW_PC + 100.
Definition EXW_GOT : Z := B_prog_val (A_OBJ 0).
Definition EXW_CELL : Z := B_prog_val (A_OBJ 12).
Definition EXW_MASK : Z := 4294977024.
Definition EXW_SB : Z := 0x7fff8000.
Definition EXW_TBL : ctable := B_prog_tbl.
Definition EXW_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition EXW_SPF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition EXW_PTRQ : afact := mkAF 4096 (2 ^ 47 - 16) 3.
Definition EXW_PTRT : afact := mkAF 4096 (2 ^ 47 - 1) 0.
Lemma exw_pc_entry : EXW_PC = B_prog_sigma AS_ex_ws.
Proof. reflexivity. Qed.
(* the GOT word and the shadow-offset cell: in the image, apart, below 2 ^ 32 (computed from the listing's atoms) *)
Lemma exw_obj_bounds : 4096 <= EXW_GOT /\ EXW_GOT + 8 <= EXW_CELL /\ EXW_CELL + 8 <= 2 ^ 32.
Proof.
unfold EXW_GOT, EXW_CELL.
let g := eval vm_compute in (B_prog_val (A_OBJ 0)) in change (B_prog_val (A_OBJ 0)) with g.
let c := eval vm_compute in (B_prog_val (A_OBJ 12)) in change (B_prog_val (A_OBJ 12)) with c.
lia.
Qed.
Lemma exw_sb_val : EXW_SB = SHADOW_OFF.
Proof. reflexivity. Qed.

Definition exw_regions : smem :=
[ stack_region 16;
YP09.mkRegion None EXW_GOT (EXW_GOT + 8) 0 0 [YP09.mkChunk EXW_GOT (CVal 8 (SLit EXW_CELL))];
YP09.mkRegion None EXW_CELL (EXW_CELL + 8) 0 0 [YP09.mkChunk EXW_CELL (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 10%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))] ].
Definition exw_facts : list (nat * afact) :=
[ (2%nat, EXW_SPF); (10%nat, EXW_PTRQ); (32%nat, mkAF EXW_SB EXW_SB 0); (33%nat, EXW_PTRT); (34%nat, EXW_PTRT) ].
Definition ss_exw : sstate := mkSS EXW_PC sr_atoms exw_regions None (mkFacts exw_facts [] []).
Definition exw_extra (p e : Z) : list word := map (Z_to_bv 64) [EXW_SB; p; e].
Definition exw_BxE : sv := SOff 32 0.
Definition exw_SHE : list shent := [mkSHE 10 0 16].
Definition exw_lregs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 11%bv (SOff 15 0))
13%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 12 0))) 16%bv (SLit 32)) 17%bv (SLit EXW_MASK)) 5%bv (SLit 1).
Definition exw_lregions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 15 0))];
YP09.mkRegion (Some 15%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition exw_lfacts : list (nat * afact) :=
[ (2%nat, EXW_SPF); (10%nat, EXW_PTRQ); (12%nat, mkAF EXW_SB EXW_SB 0); (14%nat, EXW_PTRT);
(15%nat, mkAF 4096 (2 ^ 47 - 2) 0); (32%nat, mkAF 0 255 0) ].
Definition ss_exl : sstate := mkSS EXW_LOOP exw_lregs exw_lregions None (mkFacts exw_lfacts [] []).
Definition exw_BxL : sv := SOff 12 0.
Definition exw_SHL : list shent := [mkSHE 15 0 1; mkSHE 10 0 8].

(* ---- journal-free helpers (skip_ws_x.v's, unchanged) ---- *)
Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma exw_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma exw_region_nth : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma exw_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma exw_kept : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma exw_garr8_kept : forall H (m m' : word -> option byte) p L,
(forall a, p <= a < p + Z.of_nat (length L) -> aview segs H m' a = aview segs H m a) ->
garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview segs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exw_val_kept : forall H (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma exw_ra_kept : forall H (m m' : word -> option byte) a n,
(forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.
End h.
Lemma exw_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = sb + v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id (v / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma exw_nth_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth k l 0 = b.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH k b rest H).
Qed.
Lemma exw_mask_U : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c <= 32 ->
U E (SAlu ALU_AND (SAlu ALU_SRL (SLit EXW_MASK) (SOff 32 0)) (SLit 1)) = if PjGrammar.ws c then 1 else 0.
Proof.
intros E c H Hc. rewrite !U_SAlu, (U_atom E 32 c H) by lia. rewrite !U_lit by (unfold EXW_MASK; lia).
clear H. revert Hc. generalize c. intros x Hx.
assert (A : forallb (fun y => Z.eqb (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SRL EXW_MASK y)) 1))
(if (y =? 32) || (y =? 9) || (y =? 10) || (y =? 13) then 1 else 0)) (map Z.of_nat (seq 0 33)) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A x). cbv beta in A. unfold PjGrammar.ws.
apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.
Lemma exw_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own,
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof. intros E r rs STK sp0 FP bl0 blc ly own Hw H a (r' & [<-|Hin] & Ha); [exact (Hw a Ha) | apply H; exists r'; auto]. Qed.
Lemma exw_agree2 : forall E a b, env_agree 32 E (ewset (ewset E 33 a) 34 b).
Proof. intros E a b. split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]. Qed.
Lemma exw_skipn_S : forall (l : list Z) k b rest, skipn k l = b :: rest -> skipn (S k) l = rest.
Proof. induction l as [|x l IH]; intros [|k] b rest H; cbn in H |- *; try discriminate; [injection H as -> ->; reflexivity | exact (IH k b rest H)]. Qed.
Ltac exw_awr Hqw Usp Uq :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?Usp, ?Uq in Ha;
first [ lia | left; lia | exact (proj1 (Hqw a ltac:(lia))) ] | ]);
apply awr_ok_nil.
Ltac exw_ew E1 :=
cbn [ew ewset Nat.eqb]; first [exact E1 | rewrite !ew_ewset_other by lia; exact E1].
Ltac exw_after_run HS HJ SHOK HPM :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac exw_run RUN HS HJ SHOK HPM :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W FUEL E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
exw_after_run HS HJ SHOK HPM ]
end end
end.
Ltac exw_run_to RUNTO HS HJ SHOK HPM stop :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok sg EXW_TBL K Bx BAND_SPAN SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W FUEL stop E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
exw_after_run HS HJ SHOK HPM ]
end end
end.
Ltac exw_branch HS SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (snd (sym_runN_tok sg EXW_TBL K Bx BAND_SPAN SH 1 ss)) in
lazymatch r with
| TS_stopped (SR_branch ?c ?a ?b) =>
apply (SRr_sym_branch sg W E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "exw_branch: not stuck at a branch:" r
end end
end.
Ltac exw_kept_of HFr Zs ev :=
lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
let KP := fresh "KEPT" in
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
[ apply (exw_kept rsegs E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
destruct Hin_
| cbv beta in KP ]
end.

(* ---- the walk, in the running-journal form (cgif tlzw_specX shape, as skip_ws_x.v), over the whole-range table ---- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
(* image facts of B (asyms) at image B's atoms: the GOT word the code loads (auipc / ld) and the cell it points to;
   PALib's pal_got_shadow / pal_cell (YC1fP.v:308-309) at PI_prog_B *)
Hypothesis EXW_HGOT : as_got_shadow B = EXW_GOT.
Hypothesis EXW_HCELL : as_shadow_cell B = EXW_CELL.
(* the memory invariant the walk carries: kept by the three memory changes of one runner segment (YC80x's
   srr_inv_laws: mrestrict, msteps, munrestrict); ex_ws_holds_x instantiates it to the memnorm keep *)
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis PLAW : YC80x.srr_inv_laws rsegs Pinv.
Definition texw_run (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (q text len p : Z) (txt : list Z),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - EXW_TSTK -> spZ regs <= sp0 ->
alloc_ceiling <= q -> q mod 8 = 0 -> q + 16 <= 2 ^ 47 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem rsegs (mrestrict (w_H W) memc) q 8 p -> val_mem rsegs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
4096 <= text -> amem_range text len -> text <= p <= text + len ->
garr8 rsegs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs <= q \/ q + 16 <= spZ regs - EXW_TSTK) ->
(spZ regs <= text \/ text + len <= spZ regs - EXW_TSTK) ->
SRr rsegs W (cfg_at rsegs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - EXW_TSTK <= x < spZ regs) -> ~ (q <= x < q + 8) ->
aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
val_mem rsegs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (p - text)) txt))))).
(* YCbqG's run_post_tok_AJx (YCbqG.v:988-999) with the premise Pinv (ms_mem ms') right after the journal *)
Definition exw_run_post_inv (W : world rsegs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world rsegs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok rsegs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok rsegs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
Pinv (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr rsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* YCbqG's SRr_chain_tok_AJx (YCbqG.v:1000-1029) with YA0n.SRr_msteps replaced by YC80x.SRr_msteps_inv (YC80x.v:83):
   Pinv of the start memory gives Pinv of the merged end memory *)
Lemma exw_chain_inv : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps rsegs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok rsegs (extK E K ws) (sh_ss st') msr' ->
sh_ok rsegs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exw_run_post_inv W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr rsegs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (YC80x.SRr_msteps_inv rsegs B_prog_wx Pinv PLAW W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows rsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low) with (Wr := in_wrange E (ss_mem ss));
  [exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* YCbqG's SRr_run_tok_AJx / SRr_run_to_tok_AJx (YCbqG.v:1030-1063) over exw_chain_inv, at the whole-range table *)
Lemma exw_run_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok rsegs E ss (restrict (w_H W) ms) ->
sh_ok rsegs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok rsegs EXW_TBL K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds rsegs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exw_run_post_inv W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr rsegs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_tok_sound rsegs EXW_TBL K Bx Bspan SH B_prog_tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply exw_chain_inv; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr
| exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
Lemma exw_run_to_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok rsegs E ss (restrict (w_H W) ms) ->
sh_ok rsegs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok rsegs EXW_TBL K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds rsegs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
exw_run_post_inv W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr rsegs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_to_tok_sound rsegs EXW_TBL K Bx Bspan SH B_prog_tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply exw_chain_inv; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr
| exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
Let RUN := exw_run_inv.
Let RUNTO := exw_run_to_inv.
Lemma exw_aregs : forall regs regs' : bvmap 5 word,
(forall r, In r EXW_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 2) as [->|Hr2]; [exact H2|].
assert (Hc : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; lia).
apply HK. clear -Hc. cbn in Hc.
unfold EXW_KEPT. repeat destruct Hc as [<- | Hc]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.
(* the loop head (entry + 0x64), n bytes before the end: the segment lemma of the loop (pb_ex_wsX_loop) *)
Lemma pb_ex_wsX_loop : forall (n : nat) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P (txt : list Z),
Z.of_nat n = text + len - P -> text <= P < text + len ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) ->
getr regs 10 = w64 q -> getr regs 11 = w64 P -> getr regs 15 = w64 P -> getr regs 12 = w64 EXW_SB ->
getr regs 13 = w64 (EXW_SB + q / 8) -> getr regs 14 = w64 (text + len) -> getr regs 16 = w64 32 ->
getr regs 17 = w64 EXW_MASK -> getr regs 5 = w64 1 ->
spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs -> spZ regs + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 8) 8 (bv_unsigned (getr regs 1)) ->
alloc_ceiling <= q -> q mod 8 = 0 -> q + 16 <= 2 ^ 47 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem rsegs (mrestrict (w_H W) memc) q 8 P ->
4096 <= text -> amem_range text len ->
garr8 rsegs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs + 16 <= q \/ q + 16 <= spZ regs) ->
(spZ regs + 16 <= text \/ text + len <= spZ regs) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 EXW_LOOP) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r EXW_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (spZ regs + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
val_mem rsegs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (P - text)) txt))))).
Proof.
induction n as [|n IH]; intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P txt
Hn HP HJ HPM Hra H10 H11 H15 H12 H13 H14 H16 H17 H5 Hal Hsplo Hsphi Vra Hqc Hq8 Hq47 Hqw Hqra Vq Ht4 Htam GT Hlen Htra Hdqt Hdsq Hdst; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold YK0s.ret_ok in Hra.
destruct (skipn (Z.to_nat (P - text)) txt) as [|c rest] eqn:SKP.
{ exfalso. pose proof (length_skipn (Z.to_nat (P - text)) txt) as L. rewrite SKP in L. cbn in L. lia. }
pose proof (length_skipn (Z.to_nat (P - text)) txt) as LS. rewrite SKP in LS. cbn [length] in LS.
assert (Vc : val_mem rsegs (mrestrict (w_H W) memc) (P + 0) 1 c /\ 0 <= c < 256).
{ destruct (GT (Z.to_nat (P - text)) ltac:(lia)) as [V R].
rewrite (exw_nth_skipn txt _ c rest SKP) in V, R. replace (P + 0) with (text + Z.of_nat (Z.to_nat (P - text))) by lia. auto. }
destruct Vc as [Vc Hc8].
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
remember (Ereg regs [Z_to_bv 64 c]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 EXW_SB) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E14 : ew E 14 = Z_to_bv 64 (text + len)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 P) by (subst E; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = EXW_SB) by (rewrite E12; apply unsigned_lit_small; unfold EXW_SB; lia).
assert (U14 : bv_unsigned (ew E 14) = text + len) by (rewrite E14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = P) by (rewrite E15; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_exl (restrict (w_H W) (mkst regs (Z_to_bv 64 EXW_LOOP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exl. apply exw_st_ok_full.
- unfold exw_lregs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg| |]| |]| |]| |]| |];
try (intros X; discriminate X).
+ cbn [sv_denot]. rewrite U15, Z.add_0_r. exact H11.
+ rewrite (exw_denot_shx E 10 12 q EXW_SB E10 E12) by (unfold EXW_SB; lia). exact H13.
+ exact H16.
+ exact H17.
+ exact H5.
- vm_compute. reflexivity.
- unfold exw_lregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ (spZ regs) 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia | zside | exact Vra].
+ rewrite U10. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable rsegs). apply (proj2 (Hqw (q + o) ltac:(lia))). }
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ q 0 8 (SOff 15 0) P); [cbn [sv_denot]; rewrite U15, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vq].
+ rewrite U15. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ P 0 1 (SOff 32 0) c); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | exact Vc].
- apply pairwise_disjoint_of_extents. unfold exw_lregions. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10, U15.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok exw_lfacts]. unfold afact_ok, EXW_SPF, EXW_PTRQ, EXW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U12, U14, U15, U32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold EXW_SB. repeat split; lia. }
assert (HBx : U E exw_BxL = SHADOW_OFF) by (unfold exw_BxL; rewrite (U_atom E 12 EXW_SB E12) by (unfold EXW_SB; lia); reflexivity).
assert (SHOK : sh_ok rsegs exw_BxL exw_SHL E (mrestrict (w_H W) memc)).
{ unfold exw_SHL. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E exw_BxL 15 text len P 0 1 Htra HBx); [rewrite (U_atom E 15 P E15) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E exw_BxL 10 q 16 q 0 8 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia. }
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (AG1 : env_agree 32 (Ereg regs [Z_to_bv 64 c]) Ex) by (rewrite <- HE; apply exw_agree2) end.
exw_branch HS SHOK.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
assert (WSF : PjGrammar.ws c = false)
by (unfold PjGrammar.ws; repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); [lia|] end; reflexivity).
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs EXW_TBL B_prog_tbl_ok B_prog_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ EXW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K2, K1 by assumption; reflexivity|].
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. rename Hc into Hc32.
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. rename HG into G2. clear HF HFr.
exw_branch HS SHOK.
+ rewrite branch_eq_U, (exw_mask_U _ c) in Hc by (first [exw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WSF : PjGrammar.ws c = false) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [discriminate Hc' | reflexivity]).
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. clear HF HFr HG.
eapply (SRr_ret_at rsegs EXW_TBL B_prog_tbl_ok B_prog_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ EXW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K3, K2, K1 by assumption; reflexivity|].
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
+ rewrite branch_eq_U, (exw_mask_U _ c) in Hc by (first [exw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WST : PjGrammar.ws c = true) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [reflexivity | discriminate Hc']). clear Hc.
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. rename HG into G3. clear HF HFr.
exw_branch HS SHOK.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
exw_run_to RUNTO HS HJ SHOK HPM EXW_LOOP.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K4. rename HG into G4. clear HF HFr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
aview rsegs (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a = aview rsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite K4, K3, K2, K1 by assumption; reflexivity).
assert (GALL : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
by (intros a Ha; apply (apresent_grows _ _ _ a G4), (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (15%bv : bv 5) R15. prreg HS (12%bv : bv 5) R12. prreg HS (14%bv : bv 5) R14.
prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17. prreg HS (5%bv : bv 5) R5.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ _ 13%bv HS) as R13.
lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
let e := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with e in R13;
rewrite (exw_denot_shx Ex 10 12 q EXW_SB ltac:(exw_ew E10) ltac:(exw_ew E12)) in R13 by (unfold EXW_SB; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP4 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (exw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (IH W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len (P + 1) txt);
[ lia | lia | exact HJ | exact HPM
| cbn [ms_regs]; rewrite R1, E1; exact Hra
| cbn [ms_regs]; rewrite R10, E10; reflexivity
| cbn [ms_regs]; rewrite R11, U15; reflexivity
| cbn [ms_regs]; rewrite R15, U15; reflexivity
| cbn [ms_regs]; rewrite R12, E12; reflexivity
| cbn [ms_regs]; rewrite R13; reflexivity
| cbn [ms_regs]; rewrite R14, E14; reflexivity
| cbn [ms_regs]; rewrite R16; reflexivity
| cbn [ms_regs]; rewrite R17; reflexivity
| cbn [ms_regs]; rewrite R5; reflexivity
| cbn [ms_regs]; rewrite SP4; exact Hal
| cbn [ms_regs]; rewrite SP4; exact Hsplo
| cbn [ms_regs]; rewrite SP4; exact Hsphi
| cbn [ms_regs ms_mem]; rewrite SP4, R1, E1; exact VS
| exact Hqc | exact Hq8 | exact Hq47
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (exw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (exw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (exw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP4; exact Hdsq
| cbn [ms_regs]; rewrite SP4; exact Hdst ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HPM5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split; [exact HPM5|].
split; [intros r Hr; rewrite (HK5 r Hr); exact (regs_kept_of_st_ok rsegs _ _ _ regs _ EXW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Hsp5; cbn [ms_regs]; rewrite SP4; reflexivity|].
split; [intros x Hx Hnq; rewrite (Hkp5 x Hx Hnq); exact (KALL x Hx Hnq)|].
cbn [PjGrammar.skip]. rewrite WST.
replace (Z.to_nat (P + 1 - text)) with (Datatypes.S (Z.to_nat (P - text))) in V5 by lia.
rewrite (exw_skipn_S txt _ c rest SKP) in V5. exact V5.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc.
assert (RN : rest = []) by (apply length_zero_iff_nil; lia).
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K4. clear HF HFr HG.
eapply (SRr_ret_at rsegs EXW_TBL B_prog_tbl_ok B_prog_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ EXW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K4, K3, K2, K1 by assumption; reflexivity|].
pose proof (exw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WST, RN. cbn [PjGrammar.skip length].
replace (text + len - Z.of_nat 0) with (P + 1) by lia. exact VQ.
Qed.
(* entry to return: the prologue, the alignment check, the two shadow checks of q, p >= end, and the loop *)
Theorem pb_ex_wsX : texw_run EXW_PC.
Proof.
unfold texw_run. intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q text len p txt
HJ HPM Hra H10 Hal Hstk1 Hstk2 Hqc Hq8 Hq47 Hqw Hqra Vp Ve Ht4 Htam Hpr GT Hlen Htra Hdqt Hdsq Hdst.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof exw_obj_bounds as (OB1 & OB2 & OB3).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
pose proof Hastk as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold EXW_TSTK in Hstk1, Hdsq, Hdst.
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite EXW_HGOT, EXW_HCELL in Kgot.
rewrite EXW_HCELL in Kcell.
remember (Ereg regs (exw_extra p (text + len))) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 EXW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (text + len)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = EXW_SB) by (rewrite E32; apply unsigned_lit_small; unfold EXW_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = text + len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs (exw_extra p (text + len))) E) by (rewrite <- HE; apply env_agree_refl).
assert (HS : st_ok rsegs E ss_exw (restrict (w_H W) (mkst regs (Z_to_bv 64 EXW_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exw. apply exw_st_ok_full.
- rewrite HE. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold exw_regions, stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
+ split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 EXW_GOT 8 (SLit EXW_CELL) EXW_CELL); [reflexivity | cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kgot).
+ split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 EXW_CELL 8 (SOff 32 0) SHADOW_OFF); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kcell).
+ rewrite U10. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable rsegs). apply (proj2 (Hqw (q + o) ltac:(lia))). }
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val rsegs E _ q 0 8 (SOff 33 0) p); [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vp].
* apply (chunk_ok_val rsegs E _ q 8 8 (SOff 34 0) (text + len)); [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold exw_regions, stack_region. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok exw_facts]. unfold afact_ok, EXW_SPF, EXW_PTRQ, EXW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U32, U33, U34. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold EXW_SB. repeat split; lia. }
assert (HBx : U E exw_BxE = SHADOW_OFF) by (unfold exw_BxE; rewrite (U_atom E 32 EXW_SB E32) by (unfold EXW_SB; lia); reflexivity).
assert (SHOK : sh_ok rsegs exw_BxE exw_SHE E (mrestrict (w_H W) memc)).
{ unfold exw_SHE. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E exw_BxE 10 q 16 q 0 16 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 EXW_PC) with (Z_to_bv 64 EXW_PC).
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
exw_branch HS SHOK.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p = text + len) by (destruct (Z.ltb_spec p (text + len)); [discriminate Hc | lia]). clear Hc.
exw_run RUN HS HJ SHOK HPM.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs EXW_TBL B_prog_tbl_ok B_prog_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra.
unfold YK0s.ret_ok in Hra.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low); exact HJ|].
split; [exact HPM|].
split; [exact (aregs_preserved_of_st_ok rsegs _ _ _ _ regs _ HS AGE ltac:(vm_compute; reflexivity))|].
split.
{ intros x Hx H1 H2. unfold EXW_TSTK in H1.
assert (NZ : ~ ((spZ regs - 16 <= x < spZ regs) \/ (q <= x < q + 8))) by tauto.
rewrite K2, K1 by assumption. reflexivity. }
pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. rewrite skipn_all2 by lia. cbn [PjGrammar.skip length]. replace (text + len - Z.of_nat 0) with p by lia. exact VQ.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p < text + len) by (destruct (Z.ltb_spec p (text + len)); [lia | discriminate Hc]). clear Hc.
exw_run_to RUNTO HS HJ SHOK HPM EXW_LOOP.
{ exw_awr Hqw Usp U10. }
exw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K2. rename HG into G2. clear HF HFr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ->
aview rsegs (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a = aview rsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite K2, K1 by assumption; reflexivity).
assert (GALL : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (15%bv : bv 5) R15. prreg HS (12%bv : bv 5) R12. prreg HS (14%bv : bv 5) R14.
prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17. prreg HS (5%bv : bv 5) R5.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ _ 13%bv HS) as R13.
lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
let e := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with e in R13;
rewrite (exw_denot_shx Ex 10 32 q EXW_SB ltac:(exw_ew E10) ltac:(exw_ew E32)) in R13 by (unfold EXW_SB; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP1 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs - 16)
by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (exw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (exw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (pb_ex_wsX_loop (Z.to_nat (text + len - p)) W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len p txt);
[ lia | lia | exact HJ | exact HPM
| cbn [ms_regs]; rewrite R1, E1; exact Hra
| cbn [ms_regs]; rewrite R10, E10; reflexivity
| cbn [ms_regs]; rewrite R11, E33; reflexivity
| cbn [ms_regs]; rewrite R15, E33; reflexivity
| cbn [ms_regs]; rewrite R12, E32; reflexivity
| cbn [ms_regs]; rewrite R13; reflexivity
| cbn [ms_regs]; rewrite R14, E34; reflexivity
| cbn [ms_regs]; rewrite R16; reflexivity
| cbn [ms_regs]; rewrite R17; reflexivity
| cbn [ms_regs]; rewrite R5; reflexivity
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs ms_mem]; rewrite SP1, R1, E1; replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia; exact VS
| exact Hqc | exact Hq8 | exact Hq47
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (exw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (exw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (exw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HPM5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split; [exact HPM5|].
split.
{ apply exw_aregs.
- intros r Hr. rewrite (HK5 r Hr). exact (regs_kept_of_st_ok rsegs _ _ _ regs _ EXW_KEPT HS AGE ltac:(vm_compute; reflexivity) r Hr).
- rewrite Hsp5. cbn [ms_regs]. rewrite SP1. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
split.
{ intros x Hx H1 H2. unfold EXW_TSTK in H1. rewrite (Hkp5 x Hx H2). apply KALL; [exact Hx | tauto]. }
exact V5.
Qed.
End m.

(* ---- the text at image B ---- *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis EXW_HGOT : as_got_shadow B = EXW_GOT.
Hypothesis EXW_HCELL : as_shadow_cell B = EXW_CELL.

(* the ledger reads only bytes below the allocation ceiling (the statics and the hidden heads) *)
Lemma exw_ledger_kept : forall ly S Hp (W : world rsegs) mem md mem' Lam peak cnt fail ran most own,
ARx ly S Hp W mem md ->
(forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HK (HG & HND & HB & HP).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as (AC1 & AC2).
assert (VK : forall a n v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
val_mem rsegs (mrestrict (w_H W) mem) a n v -> val_mem rsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v Ha Hn. apply (exw_val_kept rsegs (w_H W) mem mem' a n v). intros x Hx. apply HK. lia. }
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & GR).
refine (conj (VK _ _ _ _ _ G1) (conj (VK _ _ _ _ _ G2) (conj (VK _ _ _ _ _ G3) (conj (VK _ _ _ _ _ G4)
(conj (VK _ _ _ _ _ G5) (conj (conj (VK _ _ _ _ _ G6) G6r) (conj (conj (VK _ _ _ _ _ G7) G7r) GR))))))).
all: cbn [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B];
try change (Z.of_nat 8) with 8; try change (Z.of_nat 1) with 1; lia.
- revert HB. apply Forall_impl. intros [a k] (K0 & Kin & Khp & Kal & Kv). cbn [fst snd] in *.
refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Kin) as (B1 & B2 & B3 & _).
apply (VK (a - cf_head) 8%nat k); [lia | | exact Kv]. change (Z.of_nat 8) with 8.
pose proof (@cf_head_nonneg cp) as CH0.
assert (HU : exists u, a - cf_head = 16 * u).
{ exists ((a - cf_head) / 16). rewrite (Z.div_mod (a - cf_head) 16) at 1 by discriminate. rewrite B1, Z.add_0_r. reflexivity. }
assert (HV : exists v, alloc_ceiling = 4096 * v).
{ exists (alloc_ceiling / 4096). rewrite (Z.div_mod alloc_ceiling 4096) at 1 by discriminate. rewrite AC2, Z.add_0_r. reflexivity. }
destruct HU as [u Hu]. destruct HV as [v Hv]. clear B1 AC2.
revert B3. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0) as [Hz|Hz]; intros B3; lia.
Qed.

(* ex_ws at image B': the tex_ws_specX over an arbitrary allocator relation ARx with this Section's hypotheses *)
Theorem ex_ws_holds_x : tex_ws_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
unfold tex_ws_specX. intros ly S Hp W regs mem md ch q x0 i0 d x Lam peak cnt fail ran most own. cbv zeta.
intros HPRE H10 Vp Ve Hq8 Hspq Hqd HWIN HSRC HINB Hlen3 Hi0 HLED.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPRE as (HFN & _).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hastk & Hpres & Hch & HQT).
try change (@STK_ex_ws prh_img_B) with 16 in *.
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HSRC as (GT & Hx4 & Hxceil & Hxam & Hxra & _).
(* q's shadow: alx_zshadow_byte (YCbqG c3b5d0111037), the real stack's per-byte zero shadow *)
assert (Zq : range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF q 16).
{ intros z Hz. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
apply (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md z HAR). lia. }
(* the caller-window journal at entry: the engine's ajournal_x_init_W (lib/Reusable/YCbqGcallW.v) *)
assert (HJ : ajournal_x (SK := SK) rsegs B (@prh_pst prh_img_B) ARx (16 + d) (spZ regs + d) [(q, q + 8)] ly S Hp W mem md [] ly S Hp W mem md 0)
by exact (YCbqGcallW.ajournal_x_init_W (SK := SK) rsegs B (@prh_pst prh_img_B) ARx 16 d [(q, q + 8)] ly S Hp W regs mem md ch HFN HWIN).
try change (@pa_sigma B_prog_listing PI_prog_B AS_ex_ws) with EXW_PC.
(* the walk's invariant: the memnorm keep from the entry memory; its laws from YSRrMemnorm (5ffa8525936b) *)
eapply SRr_mono.
{ eapply (pb_ex_wsX SK B (@prh_pst prh_img_B) ARx LAWS EXW_HGOT EXW_HCELL
(fun m => YAkMemnorm.memnorm rsegs mem -> YAkMemnorm.memnorm rsegs m)
(YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) mem (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs))
(16 + d) (spZ regs + d) [(q, q + 8)] ly S Hp W mem md [] ly S Hp W mem md 0
regs q x0 (Z.of_nat (length x)) (x0 + i0) x);
[ exact HJ | exact (fun h => h) | exact Hra | exact H10 | exact A1 | unfold EXW_TSTK; lia | lia | lia | exact Hq8 | lia
| intros z Hz; split; [left; lia | apply Hdpres; lia]
| exact Zq
| exact Vp | exact Ve | exact Hx4 | exact Hxam | lia | exact GT | reflexivity | exact Hxra
| lia | left; lia | right; unfold EXW_TSTK; lia ]. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HMN' & Hpr & Hkept & Vq').
unfold fpostWm, fpostW, fQmn. cbv beta. exists ly, S, Hp, regs', mem', md', 0.
split; [reflexivity|]. split; [exact HJ'|].
split.
{ intros a Ha Hna. apply Hkept; [lia | unfold EXW_TSTK; lia |].
intros Hq. apply Hna. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia]. }
split; [exact Hpr|].
(* fQmn: the text's Q, then the memnorm keep from the walk's invariant *)
split; [|exact HMN'].
split; [exact (fun H => H)|].
split.
{ replace (Z.to_nat (x0 + i0 - x0)) with (Z.to_nat i0) in Vq' by (f_equal; lia). exact Vq'. }
(* Hp' = Hp, S' = S (the witness is the entry S), ablocks *)
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
apply (exw_ledger_kept ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR); [|exact HLED].
intros a Ha. apply Hkept; [lia | unfold EXW_TSTK; lia | lia].
Qed.
End k.

