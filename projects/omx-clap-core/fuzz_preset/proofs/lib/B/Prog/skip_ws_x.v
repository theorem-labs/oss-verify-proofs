(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: skip_ws of fuzz_preset's asan-ubsan image (B' = the #102 pin d663f82d7f48, unstripped twin c90d4fa54d43; skip_ws at 0x86948) in the running-journal program-walk form of cgif's tlzw_specX (YCbh.v), over YCbqG's ajournal_x; functional result by lib/Spec/PjGrammar.v's skip.
   RELOCATED from the old-pin walk (B = f8f98a95bc52, twin 3b5e1a099b53; origin/cold/h-verbs-1-skip-union ad1c5072e3e7, blob c677369102a2) by alreloc c4338d099cfb8025: the four address remarks below and the comments; the walk itself names the listing (PAImg_leaves / Listing_leaves, the #102 leaf listing) and no address. One statement change, no new walk: the q-off-image premise states image B's bounds (off_img_at IMG_LO_B IMG_TOP_B, YImgTop's per-image names; the old form off_img named image A's bounds, which differ from B's on the #102 pins). *)
(* Caller-facing premises: every premise of tskip_ws_leafX follows from those of the tskip_ws_specX (lib/A/PRH_FnReader.v: fpre, pj_in_okR, fwin, spZ regs <= q, q + 24 <= spZ regs + e, range_addressable q 24, src_rd) with the journal at (STK_skip_ws + e) (spZ regs + e); q is pj_parse's struct pj_in on the real stack (B' 0x86340 `addi a0, sp, 8`), inside that window at all six B' call sites. TL is PALibCore: PALib's A_OBJ 1 field is false at the per-function listing PI_skip_ws. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SKIP_WS_TSTK : Z := 16.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition tskip_ws_leafX (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (q text len p : Z) (txt : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SKIP_WS_TSTK -> spZ regs <= sp0 ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 -> off_img_at IMG_LO_B IMG_TOP_B q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
4096 <= text -> amem_range text len -> text <= p <= text + len ->
garr8 segs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs <= q \/ q + 16 <= spZ regs - SKIP_WS_TSTK) ->
(spZ regs <= text \/ text + len <= spZ regs - SKIP_WS_TSTK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - SKIP_WS_TSTK <= x < spZ regs) -> ~ (q <= x < q + 8) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
val_mem segs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (p - text)) txt))))).
End c.
End b.
Definition SKW_PC : Z := PAImg_leaves.img_sigma AS_skip_ws.
Definition SKW_LOOP : Z := SKW_PC + 0x64.
Definition SKW_GOT : Z := PAImg_leaves.skip_ws_obj 0.
Definition SKW_CELL : Z := PAImg_leaves.skip_ws_obj 12.
Definition SKW_MASK : Z := 4294977024.
Definition SKW_SB : Z := SHADOW_OFF.
Remark skw_pc_lit : SKW_PC = 0x86948. Proof. vm_compute. reflexivity. Qed.
Remark skw_loop_lit : SKW_LOOP = 0x869ac. Proof. vm_compute. reflexivity. Qed.
Remark skw_got_lit : SKW_GOT = 0xa2850. Proof. vm_compute. reflexivity. Qed.
Remark skw_cell_lit : SKW_CELL = 0xab6f8. Proof. vm_compute. reflexivity. Qed.
Remark skw_sb_lit : SKW_SB = 0x7fff8000. Proof. reflexivity. Qed.
Remark skw_base_pc : Listing_leaves.skip_ws_base = SKW_PC. Proof. vm_compute. reflexivity. Qed.
Definition SKW_TBL : ctable := PAImg_leaves.skip_ws_tbl.
Definition SKW_KEPT : list (bv 5) := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition SKW_SPF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition SKW_PTRQ : afact := mkAF 4096 (2 ^ 47 - 16) 3.
Definition SKW_PTRT : afact := mkAF 4096 (2 ^ 47 - 1) 0.
Definition skw_regions : smem :=
[ stack_region 16;
YP09.mkRegion None SKW_GOT (SKW_GOT + 8) 0 0 [YP09.mkChunk SKW_GOT (CVal 8 (SLit SKW_CELL))];
YP09.mkRegion None SKW_CELL (SKW_CELL + 8) 0 0 [YP09.mkChunk SKW_CELL (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 10%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))] ].
Definition skw_facts : list (nat * afact) :=
[ (2%nat, SKW_SPF); (10%nat, SKW_PTRQ); (32%nat, mkAF SKW_SB SKW_SB 0); (33%nat, SKW_PTRT); (34%nat, SKW_PTRT) ].
Definition ss_skw : sstate := mkSS SKW_PC sr_atoms skw_regions None (mkFacts skw_facts [] []).
Definition skw_extra (p e : Z) : list word := map (Z_to_bv 64) [SKW_SB; p; e].
Definition skw_BxE : sv := SOff 32 0.
Definition skw_SHE : list shent := [mkSHE 10 0 16].
Definition skw_lregs : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 11%bv (SOff 15 0))
13%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 12 0))) 16%bv (SLit 32)) 17%bv (SLit SKW_MASK)) 5%bv (SLit 1).
Definition skw_lregions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 10%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 15 0))];
YP09.mkRegion (Some 15%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition skw_lfacts : list (nat * afact) :=
[ (2%nat, SKW_SPF); (10%nat, SKW_PTRQ); (12%nat, mkAF SKW_SB SKW_SB 0); (14%nat, SKW_PTRT);
(15%nat, mkAF 4096 (2 ^ 47 - 2) 0); (32%nat, mkAF 0 255 0) ].
Definition ss_skl : sstate := mkSS SKW_LOOP skw_lregs skw_lregions None (mkFacts skw_lfacts [] []).
Definition skw_BxL : sv := SOff 12 0.
Definition skw_SHL : list shent := [mkSHE 15 0 1; mkSHE 10 0 8].
Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Lemma skw_st_ok_full : forall E pc sr regs (rs : smem) (G : facts) mem,
regs_ok E sr regs -> regions_wf rs = true -> Forall (region_ok segs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok segs E (mkSS pc sr rs None G) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)).
Proof.
intros E pc sr regs rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma skw_region_nth : forall E ss ms i r,
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma skw_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma skw_kept : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
Lemma skw_garr8_kept : forall H (m m' : word -> option byte) p L,
(forall a, p <= a < p + Z.of_nat (length L) -> aview segs H m' a = aview segs H m a) ->
garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. cbn in Hk. rewrite (mbyte_of_aview segs H H m m' (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma skw_val_kept : forall H (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview segs H m' x = aview segs H m x) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.
Lemma skw_ra_kept : forall H (m m' : word -> option byte) a n,
(forall x, a <= x < a + n -> aview segs H m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.
End h.
Lemma skw_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
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
Lemma skw_nth_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth k l 0 = b.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH k b rest H).
Qed.
Lemma skw_mask_U : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c <= 32 ->
U E (SAlu ALU_AND (SAlu ALU_SRL (SLit SKW_MASK) (SOff 32 0)) (SLit 1)) = if PjGrammar.ws c then 1 else 0.
Proof.
intros E c H Hc. rewrite !U_SAlu, (U_atom E 32 c H) by lia. rewrite !U_lit by (unfold SKW_MASK; lia).
clear H. revert Hc. generalize c. intros x Hx.
assert (A : forallb (fun y => Z.eqb (zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_SRL SKW_MASK y)) 1))
(if (y =? 32) || (y =? 9) || (y =? 10) || (y =? 13) then 1 else 0)) (map Z.of_nat (seq 0 33)) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A x). cbv beta in A. unfold PjGrammar.ws.
apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.
Lemma skw_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own,
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof. intros E r rs STK sp0 FP bl0 blc ly own Hw H a (r' & [<-|Hin] & Ha); [exact (Hw a Ha) | apply H; exists r'; auto]. Qed.
Lemma skw_agree2 : forall E a b, env_agree 32 E (ewset (ewset E 33 a) 34 b).
Proof. intros E a b. split; [intros nn Hnn; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]. Qed.
Lemma skw_skipn_S : forall (l : list Z) k b rest, skipn k l = b :: rest -> skipn (S k) l = rest.
Proof. induction l as [|x l IH]; intros [|k] b rest H; cbn in H |- *; try discriminate; [injection H as -> ->; reflexivity | exact (IH k b rest H)]. Qed.
Ltac skw_awr Hqw Usp Uq :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply skw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?Usp, ?Uq in Ha;
first [ lia | left; lia | exact (proj1 (Hqw a ltac:(lia))) ] | ]);
apply awr_ok_nil.
Ltac skw_ew E1 :=
cbn [ew ewset Nat.eqb]; first [exact E1 | rewrite !ew_ewset_other by lia; exact E1].
Ltac skw_after_run HS HJ SHOK :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac skw_run RUN HS HJ SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W FUEL E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
skw_after_run HS HJ SHOK ]
end end
end.
Ltac skw_run_to RUNTO HS HJ SHOK stop :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W FUEL stop E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
skw_after_run HS HJ SHOK ]
end end
end.
Ltac skw_branch HS SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (snd (sym_runN_tok sg SKW_TBL K Bx BAND_SPAN SH 1 ss)) in
lazymatch r with
| TS_stopped (SR_branch ?c ?a ?b) =>
apply (SRr_sym_branch sg W E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "skw_branch: not stuck at a branch:" r
end end
end.
Ltac skw_kept_of HFr Zs ev :=
lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
let KP := fresh "KEPT" in
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
[ apply (skw_kept rsegs E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
destruct Hin_
| cbv beta in KP ]
end.
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALibCore (PI := PAImg_leaves.PI_skip_ws) B.
Let RUN := SRr_run_tok_AJx (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx.
Let RUNTO := SRr_run_to_tok_AJx (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx.
Remark skw_pc_val : @pa_val _ _ PAImg_leaves.PI_skip_ws A_TEXT = SKW_PC. Proof. reflexivity. Qed.
Remark skw_sigma_pc : @pa_sigma _ _ PAImg_leaves.PI_skip_ws AS_skip_ws = SKW_PC. Proof. reflexivity. Qed.
Remark skw_got_val : @pa_val _ _ PAImg_leaves.PI_skip_ws (A_OBJ 0) = SKW_GOT. Proof. reflexivity. Qed.
Remark skw_cell_val : @pa_val _ _ PAImg_leaves.PI_skip_ws (A_OBJ 12) = SKW_CELL. Proof. reflexivity. Qed.
Lemma skw_aregs : forall regs regs' : bvmap 5 word,
(forall r, In r SKW_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK H2 r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 2) as [->|Hr2]; [exact H2|].
assert (Hc : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn; lia).
apply HK. clear -Hc. cbn in Hc.
unfold SKW_KEPT. repeat destruct Hc as [<- | Hc]; try contradiction; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
Qed.
Lemma skw_loop : forall (n : nat) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P (txt : list Z),
Z.of_nat n = text + len - P -> text <= P < text + len ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) ->
getr regs 10 = w64 q -> getr regs 11 = w64 P -> getr regs 15 = w64 P -> getr regs 12 = w64 SKW_SB ->
getr regs 13 = w64 (SKW_SB + q / 8) -> getr regs 14 = w64 (text + len) -> getr regs 16 = w64 32 ->
getr regs 17 = w64 SKW_MASK -> getr regs 5 = w64 1 ->
spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs -> spZ regs + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 8) 8 (bv_unsigned (getr regs 1)) ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem rsegs (mrestrict (w_H W) memc) q 8 P ->
4096 <= text -> amem_range text len ->
garr8 rsegs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs + 16 <= q \/ q + 16 <= spZ regs) ->
(spZ regs + 16 <= text \/ text + len <= spZ regs) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 SKW_LOOP) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
(forall r, In r SKW_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (spZ regs + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
val_mem rsegs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (P - text)) txt))))).
Proof.
induction n as [|n IH]; intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P txt
Hn HP HJ Hra H10 H11 H15 H12 H13 H14 H16 H17 H5 Hal Hsplo Hsphi Vra Hq4 Hq8 Hqam Hqw Hqra Vq Ht4 Htam GT Hlen Htra Hdqt Hdsq Hdst; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold YK0s.ret_ok in Hra.
destruct (skipn (Z.to_nat (P - text)) txt) as [|c rest] eqn:SKP.
{ exfalso. pose proof (length_skipn (Z.to_nat (P - text)) txt) as L. rewrite SKP in L. cbn in L. lia. }
pose proof (length_skipn (Z.to_nat (P - text)) txt) as LS. rewrite SKP in LS. cbn [length] in LS.
assert (Vc : val_mem rsegs (mrestrict (w_H W) memc) (P + 0) 1 c /\ 0 <= c < 256).
{ destruct (GT (Z.to_nat (P - text)) ltac:(lia)) as [V R].
rewrite (skw_nth_skipn txt _ c rest SKP) in V, R. replace (P + 0) with (text + Z.of_nat (Z.to_nat (P - text))) by lia. auto. }
destruct Vc as [Vc Hc8].
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
assert (Hqend : q + 16 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
remember (Ereg regs [Z_to_bv 64 c]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 SKW_SB) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E14 : ew E 14 = Z_to_bv 64 (text + len)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 P) by (subst E; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = SKW_SB) by (rewrite E12; apply unsigned_lit_small; rewrite ?skw_sb_lit; lia).
assert (U14 : bv_unsigned (ew E 14) = text + len) by (rewrite E14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = P) by (rewrite E15; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_skl (restrict (w_H W) (mkst regs (Z_to_bv 64 SKW_LOOP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_skl. apply skw_st_ok_full.
- unfold skw_lregs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg| |]| |]| |]| |]| |];
try (intros X; discriminate X).
+ cbn [sv_denot]. rewrite U15, Z.add_0_r. exact H11.
+ rewrite (skw_denot_shx E 10 12 q SKW_SB E10 E12) by (rewrite ?skw_sb_lit; lia). exact H13.
+ exact H16.
+ exact H17.
+ exact H5.
- vm_compute. reflexivity.
- unfold skw_lregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
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
- apply pairwise_disjoint_of_extents. unfold skw_lregions. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10, U15.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok skw_lfacts]. unfold afact_ok, SKW_SPF, SKW_PTRQ, SKW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U12, U14, U15, U32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?skw_sb_lit. repeat split; lia. }
assert (HBx : U E skw_BxL = SHADOW_OFF) by (unfold skw_BxL; rewrite (U_atom E 12 SKW_SB E12) by (rewrite ?skw_sb_lit; lia); reflexivity).
assert (SHOK : sh_ok rsegs skw_BxL skw_SHL E (mrestrict (w_H W) memc)).
{ unfold skw_SHL. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxL 15 text len P 0 1 Htra HBx); [rewrite (U_atom E 15 P E15) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxL 10 q 16 q 0 8 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam. unfold SHADOW_OFF. lia. }
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (AG1 : env_agree 32 (Ereg regs [Z_to_bv 64 c]) Ex) by (rewrite <- HE; apply skw_agree2) end.
skw_branch HS SHOK.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
assert (WSF : PjGrammar.ws c = false)
by (unfold PjGrammar.ws; repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); [lia|] end; reflexivity).
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. rename Hc into Hc32.
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. rename HG into G2. clear HF HFr.
skw_branch HS SHOK.
+ rewrite branch_eq_U, (skw_mask_U _ c) in Hc by (first [skw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WSF : PjGrammar.ws c = false) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [discriminate Hc' | reflexivity]).
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K3, K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
+ rewrite branch_eq_U, (skw_mask_U _ c) in Hc by (first [skw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WST : PjGrammar.ws c = true) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [reflexivity | discriminate Hc']). clear Hc.
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. rename HG into G3. clear HF HFr.
skw_branch HS SHOK.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
skw_run_to RUNTO HS HJ SHOK SKW_LOOP.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
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
rewrite (skw_denot_shx Ex 10 12 q SKW_SB ltac:(skw_ew E10) ltac:(skw_ew E12)) in R13 by (rewrite ?skw_sb_lit; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP4 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
pose proof (skw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (skw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (IH W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len (P + 1) txt);
[ lia | lia | exact HJ
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
| exact Hq4 | exact Hq8 | exact Hqam
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (skw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP4; exact Hdsq
| cbn [ms_regs]; rewrite SP4; exact Hdst ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split; [intros r Hr; rewrite (HK5 r Hr); exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Hsp5; cbn [ms_regs]; rewrite SP4; reflexivity|].
split; [intros x Hx Hnq; rewrite (Hkp5 x Hx Hnq); exact (KALL x Hx Hnq)|].
cbn [PjGrammar.skip]. rewrite WST.
replace (Z.to_nat (P + 1 - text)) with (Datatypes.S (Z.to_nat (P - text))) in V5 by lia.
rewrite (skw_skipn_S txt _ c rest SKP) in V5. exact V5.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc.
assert (RN : rest = []) by (apply length_zero_iff_nil; lia).
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K4. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K4, K3, K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WST, RN. cbn [PjGrammar.skip length].
replace (text + len - Z.of_nat 0) with (P + 1) by lia. exact VQ.
Qed.
Theorem skw_main : tskip_ws_leafX SK rsegs B PST ARx SKW_PC.
Proof.
unfold tskip_ws_leafX. intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q text len p txt
HJ Hra H10 Hal Hstk1 Hstk2 Hq4 Hq8 Hqam Hqoff Hqw Hqra Vp Ve Ht4 Htam Hpr GT Hlen Htra Hdqt Hdsq Hdst.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
pose proof Hastk as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold SKIP_WS_TSTK in Hstk1, Hdsq, Hdst.
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
assert (Hqend : q + 16 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
pose proof Hqoff as Hqoff'. unfold off_img_at in Hqoff'. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hqoff'.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (palc_got_shadow B TL), (palc_cell B TL), skw_got_val, skw_cell_val in Kgot.
rewrite (palc_cell B TL), skw_cell_val in Kcell.
remember (Ereg regs (skw_extra p (text + len))) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SKW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (text + len)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SKW_SB) by (rewrite E32; apply unsigned_lit_small; rewrite ?skw_sb_lit; lia).
assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = text + len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs (skw_extra p (text + len))) E) by (rewrite <- HE; apply env_agree_refl).
assert (HS : st_ok rsegs E ss_skw (restrict (w_H W) (mkst regs (Z_to_bv 64 SKW_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_skw. apply skw_st_ok_full.
- rewrite HE. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold skw_regions, stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
+ split; [rewrite ?skw_got_lit; lia|]. split; [rewrite ?skw_got_lit; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 SKW_GOT 8 (SLit SKW_CELL) SKW_CELL); [reflexivity | rewrite ?skw_cell_lit; cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kgot).
+ split; [rewrite ?skw_cell_lit; lia|]. split; [rewrite ?skw_cell_lit; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 SKW_CELL 8 (SOff 32 0) SHADOW_OFF); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kcell).
+ rewrite U10. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable rsegs). apply (proj2 (Hqw (q + o) ltac:(lia))). }
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val rsegs E _ q 0 8 (SOff 33 0) p); [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vp].
* apply (chunk_ok_val rsegs E _ q 8 8 (SOff 34 0) (text + len)); [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold skw_regions, stack_region. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite ?skw_got_lit, ?skw_cell_lit. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok skw_facts]. unfold afact_ok, SKW_SPF, SKW_PTRQ, SKW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U32, U33, U34. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?skw_sb_lit. repeat split; lia. }
assert (HBx : U E skw_BxE = SHADOW_OFF) by (unfold skw_BxE; rewrite (U_atom E 32 SKW_SB E32) by (rewrite ?skw_sb_lit; lia); reflexivity).
assert (SHOK : sh_ok rsegs skw_BxE skw_SHE E (mrestrict (w_H W) memc)).
{ unfold skw_SHE. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxE 10 q 16 q 0 16 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 SKW_PC) with (Z_to_bv 64 SKW_PC).
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
skw_branch HS SHOK.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p = text + len) by (destruct (Z.ltb_spec p (text + len)); [discriminate Hc | lia]). clear Hc.
skw_run RUN HS HJ SHOK.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra.
unfold YK0s.ret_ok in Hra.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [exact (aregs_preserved_of_st_ok rsegs _ _ _ _ regs _ HS AGE ltac:(vm_compute; reflexivity))|].
split.
{ intros x Hx H1 H2. unfold SKIP_WS_TSTK in H1.
assert (NZ : ~ ((spZ regs - 16 <= x < spZ regs) \/ (q <= x < q + 8))) by tauto.
rewrite K2, K1 by assumption. reflexivity. }
pose proof (skw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. rewrite skipn_all2 by lia. cbn [PjGrammar.skip length]. replace (text + len - Z.of_nat 0) with p by lia. exact VQ.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p < text + len) by (destruct (Z.ltb_spec p (text + len)); [lia | discriminate Hc]). clear Hc.
skw_run_to RUNTO HS HJ SHOK SKW_LOOP.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
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
rewrite (skw_denot_shx Ex 10 32 q SKW_SB ltac:(skw_ew E10) ltac:(skw_ew E32)) in R13 by (rewrite ?skw_sb_lit; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP1 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs - 16)
by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
pose proof (skw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (skw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (skw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (skw_loop (Z.to_nat (text + len - p)) W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len p txt);
[ lia | lia | exact HJ
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
| exact Hq4 | exact Hq8 | exact Hqam
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (skw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split.
{ apply skw_aregs.
- intros r Hr. rewrite (HK5 r Hr). exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AGE ltac:(vm_compute; reflexivity) r Hr).
- rewrite Hsp5. cbn [ms_regs]. rewrite SP1. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
split.
{ intros x Hx H1 H2. unfold SKIP_WS_TSTK in H1. rewrite (Hkp5 x Hx H2). apply KALL; [exact Hx | tauto]. }
exact V5.
Qed.
End m.
Theorem skip_ws_x_holds : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop) {HL : Z},
AR_laws_x rsegs B ARx HL -> PALibCore (PI := PAImg_leaves.PI_skip_ws) B ->
tskip_ws_leafX SK rsegs B PST ARx (PAImg_leaves.img_sigma AS_skip_ws).
Proof. intros fx rc SK B PST ARx HL LAWS TL. exact (skw_main SK B PST ARx LAWS TL). Qed.
