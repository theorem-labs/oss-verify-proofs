(* fuzz_preset, S1 ALLOC-HEAP, image B (asan-ubsan): the walk of fuzz_free (alloc.c :118-127; 76 slots of a Theorem Labs lane's
   whole-program listing lib/B/Listing_prog.v, entry B_entry_fuzz_free) against the text tfuzz_free_specX
   (lib/A/PRH_FnAlloc.v, room invariant room_live_cf at RL := prh_room_live_a8), at the allocator relation ARcfx (a Theorem Labs lane's ARcf pa_segs B,
   lib/Reusable/YG0ncf.v, with xs_placed_cf; YGcallcf.v's ARxs) and preset's CfParams_preset, in cgif's per-function
   form (fuzz_grant's CtrlIdentityPollBlock.v on a Theorem Labs lane's branch): YC80x / YC1fPx's runner over YCbqG's
   ajournal_x (the mixed-write twin paj_run_x_m: the frame and the static g_live), __asan_unpoison_memory_region by
   a Theorem Labs lane's aj_unpoison_x over YGcfHp's cf text, the tail jump to the free wrapper by a Theorem Labs lane's aj_free_x_ct
   at o = 0 over YG0dcf's cf text, the room by a Theorem Labs lane's YGcfRoomLive.RL_free_step at L24 + DRV + 1
   (CfRoomLivePreset.preset_rl_b24_ok), the call's QM_cf by YGcfRoomLive.room_live_room, the ledger by S1Ledger's
   prh_ledger_disown.
   #102 (this line, B' images, the kit of record walkkit-next decff67d721f): the ledger carries g_most / g_own_ran_out
   (prh_ledger .. most own; prh_pst has seven statics); the walk keeps both cells off its writes (prh_pst_most /
   prh_pst_own) and passes them through prh_glob_final_le and prh_ledger_disown (the S1Ledger.v 8cf15eeb6311).
   The body: p = 0 returns (beqz); else the UBSan checks p <> 16 / 15 <u p (`unimp` traps, decided by the engine from
   p's range: p - 16 is a live block >= 4096), unpoison (p - 16, 16), the two ASan checks of the head (decided by the
   shadow entry ff_SH: the head's shadow is 0 after the unpoison), k := the head (8 lbu, ff_hdr_U), g_live -= k (a PW
   store through an auipc base, a row of B_alias_hints), the frame popped, `j __wrap_free` with a0 = p - 16.
   Numerals: the frame 32 (LENGTH: the listing's `addi sp, sp, -32`), the head 16 / 8 / -16 / -8 (LENGTH: cf_head and
   the head word), 4096 / 4112 (the least block address, + cf_head), 16416 (DERIVED: STK_fuzz_free at prh_img_B, by
   reflexivity), 16384 / 4096 (ASTACK / ESTACK, by reflexivity), atom indices 2 / 10 / 32 / 33 / 34 and the call's
   havoc index 48 (DERIVED: the symbolic engine's numbering, cgif's convention), register numbers 1 2 3 4 8 10 11
   (WORD), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64, 63 and the byte shifts 8 .. 56 (WORD / DERIVED: the shadow span, the stack
   band, machine words and byte lanes). No ADDRESS literal: every address is a pa_val / pa_sigma of lib/B/PAImg_prog.v
   or a PrhImg field of lib/B/PRH_ImgB.v, computed where compared.
   THE RE-HIDING MOVE (the text concludes SRr' segs RZ_cf, its post fpostbm at wle' segs RZ_cf): the non-NULL arm runs
   over the R runners at wle' segs RZ_cf (YC1fPx's paj_run_x_m_invR, YCbqG's ajournal_x_initR, YGcallMxmn's
   aj_unpoison_x_mR) and calls the primed free row with the memnorm keep (YGcfMallocComposeKeep's
   afree_realizes_cf_rh_keep) by YGcallMxmnKeep's aj_free_x_ct_m_rh_keep, whose last conjunct carries memnorm across
   the free; the NULL arm keeps its plain walk and is lifted (YA0nH.SRr_SRr', YCbqGwild.apost_base_xb_of_xR at wle'
   after YCbqG.apost_base_x_R_lift). The free's call memory QMm_cf: cf_hull_ok from the text's budget
   (lib/A/PresetHullPay.v hull_ok_of_budget) and arodata_ok_cf from the entry's reader form through the journal
   (YGcallcf.v arodata_ok_cf_of_journal_P at image B's rows, lib/AU/CfAroPresetB.v), so the walk is at image B's
   CfImg_B (as the image-A walk is at CfImg_A); the hull use from the free's model path (YGcfSecsStep.secs_free_step). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre FCiface YGcallx YGcallcf YGcfHp YGcallPx YGcallPcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger S1Ccnt24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRun PresetReqAt PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfSecsStep YGcfAroBridge
  YF0m YGcfMallocComposeKeep YGcallMxmnKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB CfAroPresetB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure facts ---- *)
(* the head word as the listing's lbu / slli / or tree rebuilds it from its eight bytes (SExt false 8 of the word
   shifted right by 8 i is byte i; the engine's own value, read off the symbolic run) *)
Definition ff_hdr (v : sv) : sv :=
  SAlu ALU_OR
    (SAlu ALU_SLL
       (SAlu ALU_OR
          (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 56))) (SLit 24))
                       (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 48))) (SLit 16)))
          (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 40))) (SLit 8))
                       (SExt false 8 (SAlu ALU_SRL v (SLit 32)))))
       (SLit 32))
    (SAlu ALU_OR
       (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 24))) (SLit 24))
                    (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 16))) (SLit 16)))
       (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL v (SLit 8))) (SLit 8))
                    (SExt false 8 v))).
Lemma ff_tb_zc : forall x j, Z.testbit (zcanon x) j = if j <? 64 then Z.testbit x j else false.
Proof.
intros x j. unfold zcanon, M64. destruct (Z.ltb_spec j 64) as [H|H].
- destruct (Z.ltb_spec j 0) as [H0|H0]; [rewrite !Z.testbit_neg_r by lia; reflexivity|].
  apply Z.mod_pow2_bits_low. lia.
- apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma ff_tb_mod8 : forall x j, Z.testbit (x mod 2 ^ 8) j = if j <? 8 then Z.testbit x j else false.
Proof.
intros x j. destruct (Z.ltb_spec j 8) as [H|H].
- destruct (Z.ltb_spec j 0) as [H0|H0]; [rewrite !Z.testbit_neg_r by lia; reflexivity|].
  apply Z.mod_pow2_bits_low. lia.
- apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma ff_tb_shl : forall a n m, 0 <= n -> Z.testbit (Z.shiftl a n) m = if m <? n then false else Z.testbit a (m - n).
Proof.
intros a n m Hn. destruct (Z.ltb_spec m n) as [H|H]; [apply Z.shiftl_spec_low; lia | apply Z.shiftl_spec; lia].
Qed.
Lemma ff_tb_shr : forall a n m, 0 <= n -> Z.testbit (Z.shiftr a n) m = if m <? 0 then false else Z.testbit a (m + n).
Proof.
intros a n m Hn. destruct (Z.ltb_spec m 0) as [H|H]; [apply Z.testbit_neg_r; lia | apply Z.shiftr_spec; lia].
Qed.
Lemma ff_land63 : forall k, 0 <= k < 64 -> Z.land (zcanon k) 63 = k.
Proof.
intros k Hk. unfold zcanon, M64. rewrite Z.mod_small by lia. change 63 with (Z.ones 6).
rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia.
Qed.
Lemma ff_hdr_U : forall E v, U E (ff_hdr v) = U E v.
Proof.
intros E v. unfold ff_hdr. repeat progress (rewrite ?U_SAlu, ?U_SExt, ?U_SLit). cbn [zalu_raw Z.of_N].
rewrite !ff_land63 by lia.
pose proof (U_range E v) as Hu. unfold M64 in Hu. revert Hu. generalize (U E v) as u. intros u Hu.
apply Z.bits_inj'. intros j Hj.
repeat progress (rewrite ?ff_tb_zc, ?Z.lor_spec, ?ff_tb_mod8; rewrite ?ff_tb_shl, ?ff_tb_shr by lia).
assert (j < 8 \/ (8 <= j < 16) \/ (16 <= j < 24) \/ (24 <= j < 32) \/ (32 <= j < 40) \/ (40 <= j < 48) \/
        (48 <= j < 56) \/ (56 <= j < 64) \/ 64 <= j) as Hc by lia.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]]];
  repeat match goal with |- context [?x <? ?y] =>
    first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
          | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [orb andb]; rewrite ?Bool.orb_false_r;
  first [ reflexivity | f_equal; lia | rewrite (Z_testbit_high 64 u j) by lia; reflexivity ].
Qed.

(* membership in no write window *)
Lemma ff_not_wr : forall E rs a,
  Forall (fun r => r_whi r <= r_wlo r \/ base_val E (r_base r) + r_whi r <= a \/ a < base_val E (r_base r) + r_wlo r) rs ->
  ~ in_wrange E rs a.
Proof. intros E rs a HF (r & Hin & Hr). rewrite Forall_forall in HF. specialize (HF r Hin). lia. Qed.

Ltac ff_regs tac :=
  lazymatch goal with |- Forall ?P ?rs => let rs' := eval vm_compute in rs in change (Forall P rs') end;
  repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil end;
  cbn [YP09.r_whi YP09.r_wlo YP09.r_base YP09.r_lo YP09.r_hi base_val]; tac.

(* p's head base is 8-aligned *)
Lemma ff_mod8 : forall p, p mod 16 = 0 -> (p - 16) mod 8 = 0.
Proof.
intros p H. apply Z.mod_divide in H as [x Hx]; [|lia]. subst p.
replace (x * 16 - 16) with ((2 * x - 2) * 8) by lia. apply Z.mod_mul. lia.
Qed.
(* an application byte is none of the two shadow bytes of a heap head *)
Lemma ff_shadow_app {rc : YM05.RunCeil} : forall x a, 0 <= x < ASAN_CEIL -> app_addr a -> ~ (shadow_addr x <= a < shadow_addr x + 2).
Proof.
intros x a Hx Ha. unfold app_addr in Ha. unfold shadow_addr. pose proof ASAN_CEIL_range as HC.
assert (H0 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (H1 : x / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* the free's trace reads only sp, ra and s0 *)
Lemma ff_call_trace_eq : forall ly pc r1 r2 ch, spZ r1 = spZ r2 -> raZ r1 = raZ r2 -> s0Z r1 = s0Z r2 ->
  call_trace ly pc r1 ch = call_trace ly pc r2 ch.
Proof. intros ly pc r1 r2 ch H1 H2 H3. unfold call_trace, frame0_ok. rewrite H1, H2, H3. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* image B's cf instance: the call memory's read-only rows are image B's (lib/AU/CfAroPresetB.v) *)
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).

(* ---- the symbolic states ---- *)
(* fuzz_free's entry slot of the whole-program listing (B_entry_fuzz_free), as a byte offset from the base *)
Definition FF_PC : Z := 4 * Z.of_nat (B_prog_slot AS_fuzz_free).
Lemma ff_entry_pc : SIGMA AS_fuzz_free = BASE + FF_PC.
Proof. vm_compute. reflexivity. Qed.
(* entry: its own 32-byte frame below the entry sp (atom 2), the GOT slot of the shadow-offset cell and the cell
   (cgif's PALib convention), the shadow offset as atom 32, g_live's object fact (A_OBJ 9 of the whole-program
   listing) and h-verbs-1's alias rows (one of them is fuzz_free's g_live store) *)
Definition FF_Bx : sv := SOff 32 0.
Definition FF_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ff_regions : smem := [ stack_region 32; got_regionP; bcell_regionP 32 ].
Definition ff_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (A_OBJ 9, mkAF (VAL (A_OBJ 9)) (VAL (A_OBJ 9)) 0)] [] B_alias_hints.
Definition ss_ff : sstate := mkSS FF_PC sr_atoms ff_regions None ff_facts.
(* p <> 0: also the head word of p's block (atom 34 = its value k) and g_live (atom 33 = its value), and p's range *)
Definition ff_live_region : YP09.region := YP09.mkRegion (Some (A_OBJ 9)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition ff_head_region : YP09.region := YP09.mkRegion (Some 10%nat) (-16) (-8) 0 0 [YP09.mkChunk (-16) (CVal 8 (SOff 34 0))].
Definition ff_regions1 : smem := ff_head_region :: ff_live_region :: ff_regions.
Definition ff_facts1 : facts := mkFacts ((10%nat, mkAF 4112 (2 ^ 47) 4) :: f_atoms ff_facts) [] B_alias_hints.
Definition ss_ff1 : sstate := mkSS FF_PC sr_atoms ff_regions1 None ff_facts1.
(* after the unpoison: the head's 16 bytes read shadow 0 *)
Definition ff_SH : list shent := [mkSHE 10 (-16) 0].
Definition FF_E (regs : bvmap 5 word) (live k : Z) : env :=
  Eimg (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; live; k])).

Lemma FF_E_img : forall regs l k j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew (FF_E regs l k) j) = VAL j.
Proof. intros regs l k j Hj. unfold FF_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. Qed.
Lemma FF_E_reg : forall regs l k n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (FF_E regs l k) n = getr regs r.
Proof.
intros regs l k n r Hn. unfold FF_E. pose proof (u5_range r) as Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma FF_E_extra : forall regs l k,
  ew (FF_E regs l k) 32 = Z_to_bv 64 SHADOW_OFF /\ ew (FF_E regs l k) 33 = Z_to_bv 64 l /\ ew (FF_E regs l k) 34 = Z_to_bv 64 k.
Proof.
intros regs l k. unfold FF_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [|split]; [exact (ew_Ereg_extra regs _ 0) | exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)].
Qed.
Lemma FF_E_agree : forall regs l k, env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; l; k])) (FF_E regs l k).
Proof. intros regs l k. split; [intros n Hn; unfold FF_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

(* image numbers, computed from the generated instance, never typed *)
Lemma ff_live_obj : VAL (A_OBJ 9) = pi_g_live.
Proof. vm_compute. reflexivity. Qed.
Ltac ff_lits :=
  repeat match goal with
  | |- context [@pa_val ?r B_prog_listing PI_prog_B ?j] =>
    let v := eval vm_compute in (@pa_val r B_prog_listing PI_prog_B j) in
    change (@pa_val r B_prog_listing PI_prog_B j) with v
  | |- context [B_prog_val ?j] =>
    let v := eval vm_compute in (B_prog_val j) in change (B_prog_val j) with v end;
  cbv [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out pi_gz_live pi_gz_peak
       pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B].
Lemma ff_stk : STK_fuzz_free = 16416.
Proof. reflexivity. Qed.
Lemma ff_cf_head : cf_head = 16.
Proof. reflexivity. Qed.
(* the statics lie below the shadow (and so below any stack and above page 0) *)
Lemma ff_pst_range : forall a, Exists (in_zr a) prh_pst -> 4096 <= a < SHADOW_OFF.
Proof.
intros a Ha. unfold prh_pst in Ha. cbv [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out
  pi_gz_live pi_gz_peak pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B] in Ha.
repeat (apply Exists_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; unfold SHADOW_OFF; lia|]).
inversion Ha.
Qed.
(* g_live's eight bytes are its prh_pst entry (generated width pi_gz_live, 8 at prh_img_B) *)
Lemma ff_live_pst : forall a, pi_g_live <= a < pi_g_live + 8 -> Exists (in_zr a) prh_pst.
Proof. intros a Ha. unfold prh_pst. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
revert Ha. ff_lits. intros Ha. lia. Qed.
(* the image objects a walk keeps a region for are image bytes: the GOT slot and the shadow-offset cell (the image's
   writable segments, computed from the instance as OwnB.v's ob_img_in) and g_live (S1ImgB) *)
Ltac ff_bnd := match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end; lia.
Lemma ff_obj_in_img : forall i x, (i = 0 \/ i = 9 \/ i = 12)%nat -> VAL (A_OBJ i) <= x < VAL (A_OBJ i) + 8 -> in_img SEGS x.
Proof.
intros i x Hi Hx. destruct Hi as [ -> | [ -> | -> ] ].
- change SEGS with rsegs. unfold in_img. change (VAL (A_OBJ 0)) with (B_prog_val (A_OBJ 0)) in Hx.
  let v := eval vm_compute in (B_prog_val (A_OBJ 0)) in change (B_prog_val (A_OBJ 0)) with v in Hx.
  first [ eexists; split; [do 2 right; left; reflexivity | ff_bnd] | eexists; split; [do 3 right; left; reflexivity | ff_bnd] ].
- rewrite ff_live_obj in Hx. apply (pst_in_img_B x). apply ff_live_pst. lia.
- change SEGS with rsegs. unfold in_img. change (VAL (A_OBJ 12)) with (B_prog_val (A_OBJ 12)) in Hx.
  let v := eval vm_compute in (B_prog_val (A_OBJ 12)) in change (B_prog_val (A_OBJ 12)) with v in Hx.
  first [ eexists; split; [do 2 right; left; reflexivity | ff_bnd] | eexists; split; [do 3 right; left; reflexivity | ff_bnd] ].
Qed.

Lemma ff_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the mixed write premise: every window is the frame or g_live *)
Lemma ff_wr : forall E rs STK sp0 FP bl0 blc ly own,
  Forall (fun r => r_whi r <= r_wlo r \/
    (sp0 - STK <= base_val E (r_base r) + r_wlo r /\ base_val E (r_base r) + r_whi r <= sp0) \/
    (pi_g_live <= base_val E (r_base r) + r_wlo r /\ base_val E (r_base r) + r_whi r <= pi_g_live + 8)) rs ->
  forall a, in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ Exists (in_zr a) prh_pst.
Proof.
intros E rs STK sp0 FP bl0 blc ly own HF a (r & Hin & Hr). rewrite Forall_forall in HF.
destruct (HF r Hin) as [H|[H|H]].
- lia.
- left. unfold awr_byte. left. lia.
- right. apply ff_live_pst. lia.
Qed.

(* the memory a run leaves below its frame (the p = 0 path has no other window) *)
Ltac ff_keep0 K H rg Wx HU :=
  lazymatch type of K with
  | frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
    assert (H : forall a, 0 <= a < spZ rg - 32 -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
      by (intros a Ha; apply (ff_aview_of_frame Wx Ex rsx mA mB a K); [|lia];
          apply ff_not_wr; ff_regs ltac:(rewrite ?HU; lia))
  end.

(* an 8-byte value chunk of a region is the little-endian word of its value *)
Lemma ff_val_mem_chunk8 : forall (E : env) (m : word -> option byte) base v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk 0 (CVal 8 v)) -> val_mem SEGS m base 8 (U E v).
Proof.
intros E m base v HC. pose proof (U_range E v) as HR. unfold M64 in HR.
apply (prh_val_mem_hdr8 (L := B_prog_listing) (PA := PI_prog_B) m base (U E v) HR).
intros k Hk. destruct (HC (Z.of_nat k) ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-. rewrite Z.add_0_r in Hb2. rewrite Hb2. reflexivity.
Qed.
(* the facts a stretch keeps: frame_of off its write windows (the frame and g_live) *)
Ltac ff_keep1 K H rg Wx HU HL :=
  lazymatch type of K with
  | frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
    assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 32 <= a < spZ rg) -> ~ (pi_g_live <= a < pi_g_live + 8) ->
                aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
      by (intros a Ha Hn1 Hn2; apply (ff_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
          apply ff_not_wr; ff_regs ltac:(rewrite ?HU, ?HL; lia))
  end.


Section f.
Variable B : asyms.
(* the allocator relation of the walk (S1KitAlloc's ARxs, YGcallcf.v): ARcf with the error-buffer extents placed *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* ---- Section hypotheses: callee texts and marked stand-ins only ---- *)
(* callee text: the free wrapper, primed (a free re-hides shadow, so the run ends at wle' segs RZ_cf), with the memnorm
   keep at the leaf (YGcfMallocComposeKeep.v) *)
Hypothesis AFREE : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep SEGS B.
(* callee text: __asan_unpoison_memory_region at the second allocator (YGcfHp.v) *)
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* STAND-IN for the unit's image binding of B (CfImg for image B; owner h-mani-a8), proved once by the final instance *)
Hypothesis pal_unpoison : SIGMA AS___asan_unpoison_memory_region = cf_pc_unpoison.
(* STAND-IN for the unit's TFIB symbol binding of B (image binding, no state; the instance's TfibB_syms): errno's
   place, apart from the read-only ranges of the call memory's arodata_ok_cf (CfAroPresetB.errno_relro_preset_AU) *)
Hypothesis TS : YF0m.TfibSyms B.

(* the allocator's laws: h-mani-a8's AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge *)
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let AUNPOISONx : aunpoison_realizes_x SEGS B ARcfx cf_head cf_pc_unpoison := aunpoison_realizes_cf_xs SEGS B AUNPOISON.
Lemma ff_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a Ha. split; [exact (pst_in_img_B a Ha) | exact (proj1 (pal_pst_ok a Ha))]. Qed.
(* alloc.c's statics are no byte the call memory's arodata_ok_cf covers: each such byte is a read-only image byte
   (RELRO, or a report read inside a non-writable segment, CfAroPresetB.ro_reads_nw_preset_AU), and no static is one
   (S1ImgB.pst_not_ro_B) *)
Lemma ff_pst_aro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) prh_pst.
Proof.
intros a Ha Hx. apply (pst_not_ro_B a Hx). destruct Ha as [Ha | Ha].
- right. unfold B_prog_relro_lo, B_prog_relro_hi. cbv [cf_relro_lo cf_relro_hi CfImgB.CfImg_B] in Ha.
  exact Ha.
- left. pose proof CfAroPresetB.ro_reads_nw_preset_AU as RONW.
  unfold YGcfAroBridge.ro_reads_nw_t in RONW. rewrite Forall_forall in RONW.
  apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  destruct (RONW r Hr) as (_ & sg & Hin & NW & L & R). exists sg. split; [exact Hin|]. split; [exact NW | lia].
Qed.
Let RUN := @paj_run_x_m fx rc SK B_prog_listing PL_prog_B PA B prh_pst ARcfx _ LAWS ff_pst_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (h-hpreset-7's carrier, YSRrMemnorm.v:40) *)
Let RUNM (m0 : word -> option byte) := @paj_run_x_m_inv fx rc SK B_prog_listing PL_prog_B PA B prh_pst ARcfx _ LAWS
  ff_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
(* the same runner over the walk's world relation wle' segs RZ_cf (the free re-hides shadow) *)
Let RUNMR (m0 : word -> option byte) := @paj_run_x_m_invR fx rc SK B_prog_listing PL_prog_B PA B prh_pst ARcfx _ LAWS
  ff_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))
  (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let BR := @paj_branch fx rc B_prog_listing PA.
Let RET := @paj_ret_at fx rc B_prog_listing PL_prog_B PA.

(* a block byte is no image byte (the allocator's client-image law) *)
Lemma ff_blk_not_img : forall ly S Hp W mem md b m x,
  ARcfx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> b <= x < b + req_size m -> ~ in_img SEGS x.
Proof.
intros ly S Hp W mem md b m x HAR Hin Hx.
exact (proj2 (alx_client_img SEGS B ARcfx LAWS ly S Hp W mem md x HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Hx)))))).
Qed.
(* the head word of a live block of user size n >= 0 misses an 8-byte image object *)
Lemma ff_head_obj_disj : forall ly S Hp W mem md p n lo,
  ARcfx ly S Hp W mem md -> In (p - 16, n + 16) (ablocks B ly S) -> 0 <= n ->
  (forall x, lo <= x < lo + 8 -> in_img SEGS x) ->
  p + -8 <= lo + 0 \/ lo + 8 <= p + -16.
Proof.
intros ly S Hp W mem md p n lo HAR Hin Hn Himg.
destruct (Z_le_gt_dec (p + -8) (lo + 0)) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + 8) (p + -16)) as [H'|H']; [right; exact H'|].
exfalso. apply (ff_blk_not_img ly S Hp W mem md (p - 16) (n + 16) (Z.max (p - 16) lo) HAR Hin).
- unfold req_size. destruct (n + 16 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. lia.
- apply Himg. lia.
Qed.
(* a harness head lies below the allocator ceiling *)
Lemma ff_head_range : forall ly S Hp W mem md Lam peak cnt fail ran most own a k i,
  ARcfx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> 0 <= i < 8 ->
  4096 <= a - cf_head + i < alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k i HAR HL Hin Hi.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk & Hb & _).
destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hb) as (_ & H4096 & Hceil & _).
rewrite ff_cf_head in *. unfold req_size in Hceil. destruct (k + 16 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. lia.
Qed.
(* fpost is monotone in its post *)
Lemma ff_fpost_mono : forall STK FP regs ly S Hp (W : world SEGS) mem md
  (Q Q' : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  (forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
  fpost B ARcfx SK STK FP regs ly S Hp W mem md Q W' c' -> fpost B ARcfx SK STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q Q' W' c' HQ H. unfold fpost, apost_base_x in *.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & Hq).
exists ly', S', Hp', regs', mem', md', k. auto.
Qed.
(* the budgeted post (PRH_Base.fpostb) is monotone in its post *)
Lemma ff_fpostb_mono : forall (P : list (list Z) -> Prop) STK FP regs ly S Hp (W : world SEGS) mem md
  (Q Q' : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  (forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
  fpostb B ARcfx SK P STK FP regs ly S Hp W mem md Q W' c' -> fpostb B ARcfx SK P STK FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros P STK FP regs ly S Hp W mem md Q Q' W' c' HQ H. unfold fpostb, YCbqGwild.apost_base_xbR in *.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HB & HJ & HP & Hq).
exists ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HP | exact (HQ _ _ _ _ _ _ _ Hq)].
Qed.

(* ---- entry ---- *)
Lemma ff_entry : forall ly S Hp W regs mem md ch l k,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (FF_E regs l k) ss_ff (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FF_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS FF_Bx [] (FF_E regs l k) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch l k HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). rewrite ff_stk in *.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_const SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
set (E := FF_E regs l k).
destruct (FF_E_extra regs l k) as (E32 & _ & _). fold E in E32.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (FF_E_reg _ _ _ 2 2%bv eq_refl); reflexivity).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; subst E; apply FF_E_img; exact Hj).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (Dv : forall (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. cbn [sv_denot]. rewrite Hn, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j) by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
rewrite restrict_mkst_fx. split.
- unfold ss_ff. apply pa_entry_st_ok_full.
  + subst E. unfold FF_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ff_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
      split; [lia|]. split; [ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
      split; [lia|]. split; [ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold ff_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. ff_lits.
    repeat split; lia.
  + split; [|split; [exact I | apply B_alias_hints_ok; exact HEI]].
    unfold ff_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. ff_lits.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- p = 0: the frame, beqz taken, the epilogue, ret ---- *)
Lemma ff_p0 : forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  getr regs 10 = w64 0 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_fuzz_free) regs mem md)
    (fpost B ARcfx SK STK_fuzz_free [] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       S' = S /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\ prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem'))).
Proof.
intros ly S Hp W regs mem md ch Lam peak cnt fail ran most own HPRE H10 HL.
pose proof (@pa_segs_low _ B_prog_listing PI_prog_B) as Hsegs.
destruct (ff_entry ly S Hp W regs mem md ch 0 0 HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARcfx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_fuzz_free = 16416) by exact ff_stk.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
remember (FF_E regs 0 0) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (FF_E_reg _ _ _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (FF_E_reg _ _ _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (FF_E_reg _ _ _ 10 10%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; 0; 0])) E) by (subst E; apply FF_E_agree).
clear HE.
unfold cfg_at. change (w64 (SIGMA AS_fuzz_free)) with (Z_to_bv 64 (BASE + FF_PC)).
(* the frame and the saves; stop at beqz a0 *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FF_Bspan; [apply ff_wr; ff_regs ltac:(rewrite ?Usp, ?WS; lia) |].
clear HF HG. ff_keep0 HFr KA regs W Usp. clear HFr.
psrr_branch_tok RUN BR HS SHOK FF_Bspan.
2:{ (* beqz not taken: a0 is 0 *)
  exfalso. rewrite branch_eq_U, (U_atom E 10 0), U_SLit in Hc by (first [lia | rewrite E10, H10; reflexivity]).
  vm_compute in Hc. discriminate Hc. }
(* the epilogue; stop at ret *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM FF_Bspan; [apply ff_wr; ff_regs ltac:(rewrite ?Usp, ?WS; lia) |].
clear HF HG. ff_keep0 HFr KB regs W Usp. clear HFr.
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fpost, apost_base_x.
eexists ly, S, Hp, _, _, _, 0.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B prh_pst ARcfx LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [|exact HPM].
lazymatch goal with |- prh_ledger _ _ _ _ _ ?mT _ _ _ _ _ _ _ =>
  assert (KS : forall a, 0 <= a < spZ regs - 32 -> aview SEGS (w_H W) mT a = aview SEGS (w_H W) mem a)
    by (intros a Ha; cbn [ms_mem]; rewrite (KB a Ha); exact (KA a Ha)) end.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W); [exact HL | | | | apply Permutation_refl].
- intros a Ha. pose proof (ff_pst_range a Ha). apply KS. unfold SHADOW_OFF in *. lia.
- intros a k0 i Hin Hi. pose proof (ff_head_range ly S Hp W mem md Lam peak cnt fail ran most own a k0 i HAR HL Hin Hi). apply KS. lia.
- intros a k0 _ H. exact H.
Qed.

(* entry, p <> 0: also p's head word (atom 34 = its value) and g_live (atom 33 = its value) *)
Lemma ff_entry1 : forall ly S Hp W regs mem md ch p n live,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  getr regs 10 = w64 p -> 0 <= n -> In (p - 16, n + 16) (ablocks B ly S) -> p mod 16 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) (p - 16) 8 n ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_live 8 live -> 0 <= live < 2 ^ 64 ->
  st_ok_pi SEGS VAL (FF_E regs live n) ss_ff1 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + FF_PC)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS FF_Bx [] (FF_E regs live n) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch p n live HPRE H10 Hn Hblk Hp16 Hhd Hlive Rlive.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). rewrite ff_stk in *.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md _ _ HAR Hblk) as (Hb16 & Hb4096 & Hbceil & _).
assert (RQ : req_size (n + 16) = n + 16)
  by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite RQ in Hbceil.
destruct (alx_const SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (ff_head_obj_disj ly S Hp W mem md p n (VAL (A_OBJ 0)) HAR Hblk Hn
  (fun x Hx => ff_obj_in_img 0 x (or_introl eq_refl) Hx)) as D0.
pose proof (ff_head_obj_disj ly S Hp W mem md p n (VAL (A_OBJ 9)) HAR Hblk Hn
  (fun x Hx => ff_obj_in_img 9 x (or_intror (or_introl eq_refl)) Hx)) as D9.
pose proof (ff_head_obj_disj ly S Hp W mem md p n (VAL (A_OBJ 12)) HAR Hblk Hn
  (fun x Hx => ff_obj_in_img 12 x (or_intror (or_intror eq_refl)) Hx)) as D12.
set (E := FF_E regs live n).
destruct (FF_E_extra regs live n) as (E32 & E33 & E34). fold E in E32, E33, E34.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (FF_E_reg _ _ _ 2 2%bv eq_refl); reflexivity).
assert (Up : bv_unsigned (ew E 10) = p)
  by (subst E; rewrite (FF_E_reg _ _ _ 10 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j) by (intros j Hj; subst E; apply FF_E_img; exact Hj).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (Dv : forall (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 v).
{ intros k v Hk Hv. cbn [sv_denot]. rewrite Hk, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j) by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
rewrite restrict_mkst_fx. split.
- unfold ss_ff1. apply pa_entry_st_ok_full.
  + subst E. unfold FF_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ff_regions1, ff_head_region, ff_live_region, ff_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Up. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ (-16) 8 (SOff 34 0) n); [apply Dv; [exact E34 | lia] | lia | lia |].
      replace (p + -16) with (p - 16) by lia. exact Hhd.
    * rewrite ff_live_obj. split; [ff_lits; lia|]. split; [ff_lits; lia|].
      split; [intros q Hq; apply pst_writable_B; apply ff_live_pst; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 33 0) live); [apply Dv; [exact E33 | lia] | lia | lia |].
      rewrite Z.add_0_r. exact Hlive.
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
      split; [lia|]. split; [ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
      split; [lia|]. split; [ff_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold ff_regions1, ff_head_region, ff_live_region, ff_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Up.
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert D0 D9 D12. ff_lits. intros D0 D9 D12.
    repeat split; lia.
  + split; [|split; [exact I | apply B_alias_hints_ok; exact HEI]].
    unfold ff_facts1, ff_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Up, Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. ff_lits.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- p <> 0: the frame, unpoison (p - 16, 16), the head k, g_live -= k, the tail jump to the free wrapper; over
   wle' segs RZ_cf (the primed free re-hides shadow). The memnorm keep: the runners' carrier to the tail call, then
   the keep rule's last conjunct across the free ---- *)
Lemma ff_nz : forall ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own,
  afn_pre_x SEGS B ARcfx STK_fuzz_free ly S Hp W regs mem md ch ->
  YGcfRoomLive.room_live_cf S -> YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S [] ->
  PresetRodata.arodata_okP SEGS cf_relro_lo cf_relro_hi B (aview SEGS (w_H W) mem) ->
  admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
  getr regs 10 = w64 p -> In (p, n) Lam ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_fuzz_free) regs mem md)
    (fpostb B ARcfx SK (YCbqGwild.wbudget [call_trace ly (pc_free_ra0 (as_code B)) regs ch] 0)
      STK_fuzz_free (ablocks_fp [(p - cf_head, n + cf_head)]) regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' => YGcfRoomLive.room_live_cf S' /\
        Hp' = remove Z.eq_dec (p - cf_head) Hp /\
        (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
        (* the run position across this free (the HFr and HBulk events of tfuzz_free_specX's arms) *)
        (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
           nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HFr (n + cf_head)) ->
           exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S') /\
        (forall sm x os i L k H0 hb, nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HBulk L) ->
           nth_error L k = Some (n + cf_head) ->
           PresetRoomPosKeep.iface_room_pos_bulk sm x os i L k H0 hb S ->
           exists hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i L (Datatypes.S k) H0 hb' S') /\
        YGcfRoomLive.ccnt24 S' + Z.of_nat (PresetRoom.ccnt YG00.kBatchClass [n + cf_head]) = YGcfRoomLive.ccnt24 S /\
        PresetHullBudget.hull_used S S' [] /\
        (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem') /\
        exists l1 l2, Lam = l1 ++ (p, n) :: l2 /\ prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own HPRE HRL HC24 HHUL HROD Htr H10 Hin HL.
assert (Hcf : cf_head = 16) by reflexivity. rewrite !Hcf.
pose proof (@pa_segs_low _ B_prog_listing PI_prog_B) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as HCR. unfold ASAN_CEIL in HCR.
assert (WS : STK_fuzz_free = 16416) by exact ff_stk.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the ledger at p *)
pose proof HL as HL0. apply prh_ledger_iff in HL0 as [HGl HLB].
pose proof HGl as (Glive & Gpeak & Gcnt & Gfail & Gran & Gmost & Gown & Rlp & Rpk & Rcnt & Rfail & Rran).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p n most own HL Hin) as (Hn & Hblk & HinHp & Hp16 & Hhd).
rewrite Hcf in Hblk, HinHp, Hhd.
pose proof HLB as (HND & HFA & HPERM).
destruct (in_split _ _ Hin) as (l1 & l2 & ELam).
assert (HF0 : Forall (fun ak => 0 <= snd ak) Lam) by (eapply Forall_impl; [|exact HFA]; intros [a k] (Hk & _); exact Hk).
assert (Hl12 : 0 <= Ledger.lsum (l1 ++ l2)).
{ apply prh_lsum_nonneg. rewrite ELam in HF0. apply Forall_app in HF0 as [HF1 HF2].
  apply Forall_app. split; [exact HF1 | exact (Forall_inv_tail HF2)]. }
assert (Hsum : Ledger.lsum Lam = Ledger.lsum (l1 ++ l2) + n) by (rewrite ELam; apply prh_lsum_split).
assert (Hnp : forall a ka, In (a, ka) (l1 ++ l2) -> a <> p).
{ intros a ka Ha ->. rewrite ELam, map_app in HND. cbn [map fst] in HND. apply NoDup_ListNoDup in HND. apply NoDup_remove_2 in HND.
  apply HND. rewrite <- map_app. change p with (fst (p, ka)). apply in_map. exact Ha. }
assert (Hsub : forall a ka, In (a, ka) (l1 ++ l2) -> In (a, ka) Lam).
{ intros a ka Ha. rewrite ELam. apply in_app_or in Ha as [Ha|Ha]; apply in_or_app; [left | right; right]; exact Ha. }
(* p's block *)
destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md (p - 16) (n + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
assert (Hp8 : (p - 16) mod 8 = 0) by exact (ff_mod8 p Hp16).
assert (Hpc : 0 <= p - 16 < ASAN_CEIL) by (unfold ASAN_CEIL; lia).
(* the entry state *)
destruct (ff_entry1 ly S Hp W regs mem md ch p n (Ledger.lsum Lam) HPRE H10 Hn Hblk Hp16 Hhd Glive ltac:(lia))
  as [HS SHOK].
pose proof (ajournal_x_initR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle'_refl SEGS YGcfRehidePost.RZ_cf) STK_fuzz_free (ablocks_fp [(p - 16, n + 16)])
  ly S Hp W regs mem md ch HPRE) as HJ.
remember (FF_E regs (Ledger.lsum Lam) n) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold FF_E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (FF_E_reg _ _ _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (FF_E_reg _ _ _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (FF_E_reg _ _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (FF_E_reg _ _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (FF_E_reg _ _ _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (FF_E_reg _ _ _ 10 10%bv eq_refl)).
assert (EX : ew E 32 = Z_to_bv 64 SHADOW_OFF /\ ew E 33 = Z_to_bv 64 (Ledger.lsum Lam) /\ ew E 34 = Z_to_bv 64 n)
  by (subst E; apply FF_E_extra).
destruct EX as (E32 & E33 & E34).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; Ledger.lsum Lam; n])) E) by (subst E; apply FF_E_agree).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Up : bv_unsigned (ew E 10) = p) by (rewrite E10, H10; apply unsigned_lit_small; lia).
pose proof HEI as HEIu. unfold img_env in HEIu.
assert (HV9 : bv_unsigned (ew E (A_OBJ 9)) = pi_g_live)
  by (rewrite (HEIu (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact ff_live_obj).
let v := eval vm_compute in (A_OBJ 9) in change (A_OBJ 9) with v in HV9.
unfold cfg_at. rewrite ff_entry_pc. change (w64 (BASE + FF_PC)) with (Z_to_bv 64 (BASE + FF_PC)).
(* ==== stretch 1: the frame, the checks p <> 0 / p <> 16 / 15 <u p (decided by p's range), the GOT and shadow
   loads, the unpoison arguments; stop at the call ==== *)
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv (RUNMR mem) HS HJ SHOK HPM FF_Bspan; [apply ff_wr; ff_regs ltac:(rewrite ?Usp, ?HV9, ?WS; lia) |].
clear HF HG. ff_keep1 HFr KA regs W Usp HV9. clear HFr.
(* ==== unpoison (p - 16, 16): S1KitPoison's aj_unpoison_x over the cf text ==== *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (@YGcallMxmn.aj_unpoison_x_mR fx rc SK SEGS B prh_pst ARcfx cf_head _ LAWS Hsegs
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)
    cf_pc_unpoison AUNPOISONx
    W E _ ms STK_fuzz_free (spZ regs) (ablocks_fp [(p - 16, n + 16)]) ly S Hp W mem md [] ly S Hp _ 0
    (p - 16) (n + 16) (-32) (ew E 2) _ HS).
  - cbn [ss_pc setpc]. exact pal_unpoison.
  - reflexivity.
  - exact HJ.
  - rewrite Ra0, Up. unfold w64. f_equal; lia.
  - rewrite Ra1, Hcf. reflexivity.
  - rewrite Hcf. reflexivity.
  - exact HinHp.
  - exact Hblk.
  - rewrite Hcf, Hreq. lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ ms 2%bv HS).
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Rgp, E3. exact Hgp.
  - rewrite Rtp, E4. exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PI_prog_B)); [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hshd & Hkeep & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
clear HJ.
rewrite Hcf in Hshd, Hkeep. change (16 / 8) with 2 in Hkeep.
(* back at the return slot: p's head, g_live and the frame are kept by the call *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK2 : tq); [|specialize (HS2 HRK2); clear HRK2] end.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
  cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Up in Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia | lia |].
    apply (ff_shadow_app (p - 16) a Hpc). apply (in_app_addr _ _ a Happ); lia.
  - lia.
  - rewrite HV9 in Ha. pose proof (ff_pst_range a) as Hr.
    assert (Ha' : Exists (in_zr a) prh_pst) by (apply ff_live_pst; lia).
    specialize (Hr Ha'). unfold SHADOW_OFF in Hr. apply (mbyte_of_aview SEGS). apply Hkeep; [lia | lia |].
    unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (p - 16) 8 ltac:(lia) ltac:(lia)). lia.
  - intros _. apply pst_writable_B. rewrite HV9 in Ha. apply ff_live_pst. lia.
  - rewrite Usp in Ha. apply (mbyte_of_aview SEGS). apply Hkeep; [lia | lia |].
    unfold shadow_addr, SHADOW_OFF. assert ((p - 16) / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia). lia.
  - intros _. apply (apresent_writable SEGS). apply HJpres2. rewrite Usp in Ha. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E')
  by (rewrite HE'; apply (img_env_havoc (L := B_prog_listing) (PI := PI_prog_B)); [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 48)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; Ledger.lsum Lam; n])) E')
  by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
assert (HV9' : bv_unsigned (ew E' (A_OBJ 9)) = pi_g_live).
{ pose proof HEI' as HEIu'. unfold img_env in HEIu'.
  rewrite (HEIu' (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). exact ff_live_obj. }
let v := eval vm_compute in (A_OBJ 9) in change (A_OBJ 9) with v in HV9'.
(* the head's two shadow bytes read 0 *)
assert (SHOK' : sh_ok SEGS FF_Bx ff_SH E' (mrestrict (w_H W) mem2)).
{ unfold ff_SH, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem2 E' FF_Bx 10%nat (p - 16) 16 p (-16) 0).
  - apply (zero_shadow_range (aview SEGS (w_H W) mem2) SHADOW_OFF (p - 16) 16 Hp8 eq_refl).
    intros i Hi. change (16 / 8) with 2 in Hi.
    replace (shadow_of_addr SHADOW_OFF (p - 16) + i) with (shadow_addr (p - 16 + i * 8))
      by (unfold shadow_addr, shadow_of_addr; rewrite Z.div_add by lia; lia).
    apply Hshd. lia.
  - unfold U, FF_Bx. cbn [sv_denot]. rewrite (OLD 32%nat) by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  - unfold U. cbn [sv_denot]. rewrite (OLD 10%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Up.
  - lia.
  - lia.
  - intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg in Hx'. unfold SHADOW_OFF. lia. }
clear SHOK.
(* ==== stretch 2: the two head shadow checks (decided by ff_SH), k := the head (8 lbu), g_live -= k, the frame
   popped, a0 = p - 16; stop at the tail jump to the free wrapper ==== *)
paj_run_tok_x_inv (RUNMR mem) HS HJ2 SHOK' HPM FF_Bspan; [apply ff_wr; ff_regs ltac:(rewrite ?Usp', ?HV9', ?WS; lia) |].
lazymatch type of HS with context [restrict _ ?msx] => rename msx into ms3 end.
clear HF HG. ff_keep1 HFr KB regs W Usp' HV9'. clear HFr.
(* g_live after the store: the live count minus the head *)
assert (Hlive3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms3)) pi_g_live 8 (Ledger.lsum (l1 ++ l2))).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMO & _). cbn [ms_mem restrict ss_mem setpc] in HMO.
  apply Forall_inv_tail in HMO. apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HMO).
  cbn [YP09.r_chunks YP09.r_base base_val] in HMO. apply Forall_inv in HMO.
  apply ff_val_mem_chunk8 in HMO.
  lazymatch type of HMO with val_mem _ _ ?b _ (U _ ?v) =>
    change v with (SAlu ALU_SUB (SOff 33 0) (ff_hdr (SOff 34 0))) in HMO end.
  rewrite U_SAlu, ff_hdr_U, !U_SOff in HMO. rewrite (OLD 33%nat), (OLD 34%nat) in HMO by lia.
  rewrite E33, E34, !unsigned_lit_small in HMO by lia. rewrite !Z.add_0_r in HMO. cbn [zalu_raw] in HMO.
  unfold zcanon, M64 in HMO. rewrite (Z.mod_small (Ledger.lsum Lam)), (Z.mod_small n), (Z.mod_small (_ - _)) in HMO by lia.
  rewrite HV9' in HMO. replace (Ledger.lsum (l1 ++ l2)) with (Ledger.lsum Lam - n) by lia. exact HMO. }
(* ==== the tail jump: YGcallx's aj_free_x_ct at o = 0 (the entry ra, sp and s0) ==== *)
prreg HS (10%bv : bv 5) Fa0. prreg HS (2%bv : bv 5) Fsp. prreg HS (1%bv : bv 5) Fra.
prreg HS (3%bv : bv 5) Fgp. prreg HS (4%bv : bv 5) Ftp. prreg HS (8%bv : bv 5) Fs0.
assert (Fsp' : spZ (ms_regs ms3) = spZ regs) by (unfold spZ at 1; rewrite Fsp, ?OLD by lia; rewrite E2; reflexivity).
assert (Fra' : getr (ms_regs ms3) 1 = getr regs 1) by (rewrite Fra, ?OLD by lia; exact E1).
assert (Fs0' : s0Z (ms_regs ms3) = s0Z regs) by (unfold s0Z at 1; rewrite Fs0, ?OLD by lia; rewrite E8; reflexivity).
assert (Fra'' : raZ (ms_regs ms3) = raZ regs) by (unfold raZ at 1; rewrite Fra'; reflexivity).
(* the memory above the entry sp is the entry's: the caller chain *)
assert (Kup : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite (KB a ltac:(lia) ltac:(lia) ltac:(pose proof (ff_pst_range pi_g_live ltac:(apply ff_live_pst; lia)); unfold SHADOW_OFF in *; lia)).
  rewrite (Hkeep a ltac:(lia) ltac:(lia) ltac:(unfold shadow_addr, SHADOW_OFF; assert ((p - 16) / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia); lia)).
  apply KA; [lia | lia |]. pose proof (ff_pst_range pi_g_live ltac:(apply ff_live_pst; lia)). unfold SHADOW_OFF in *. lia. }
(* the call memory QMm_cf at the tail call: the room from room_live_room, cf_hull_ok from the text's budget
   (PresetHullPay.hull_ok_of_budget), arodata_ok_cf from the entry's reader form through the journal to the tail
   (arodata_ok_cf_of_journal_P at image B's rows; its footprint, the freed block, opens no sink) *)
assert (HAROT : arodata_ok_cf SEGS B (ms_mem ms3)).
{ apply (arodata_ok_cf_of_journal_P (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS YGcfRehidePost.RZ_cf)
    STK_fuzz_free (spZ regs) (ablocks_fp [(p - 16, n + 16)]) ly S Hp W mem md [] ly S
    (remove Z.eq_dec (p - 16) Hp) W (ms_mem ms3) _ 0 [] HJ2
    CfAroPresetB.relro_seg_preset_AU (CfAroPresetB.errno_relro_preset_AU B TS)
    CfAroPresetB.relro_top_preset_AU CfAroPresetB.ro_reads_nw_preset_AU ff_pst_aro).
  - apply YCbq.sink_closed_ablocks_fp. constructor; [cbn [fst]; lia | constructor].
  - exact HROD. }
assert (HQM : QMm_cf SEGS B S (ms_mem ms3)).
{ destruct (QM_cf_of_room SEGS B ly S Hp W mem md (proj1 HAR) HQT (YGcfRoomLive.room_live_room S HRL)
    (PresetHullPay.hull_ok_of_budget S [] HHUL)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 HAROT)))))). }
pose proof (universe_ok_of_ARcf SEGS B ly S Hp W mem md (proj1 HAR)) as HUok.
pose proof (alloc_model_laws_x_cf B HUok) as AMX.
(* the tail call's trace: the text's admitted trace at the tail call's registers (the same trace: sp, ra, s0 kept) *)
assert (HTRT : admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms3) ch) S)
  by (rewrite (ff_call_trace_eq ly _ (ms_regs ms3) regs ch Fsp' Fra'' Fs0'); exact Htr).
eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YGcallMxmnKeep.aj_free_x_ct_m_rh_keep (SK := SK) SEGS B prh_pst LAWS Hsegs (pal_env B PAL) OWNLOW WFL AMX AFREE
    W E' _ ms3 STK_fuzz_free (spZ regs) (ablocks_fp [(p - 16, n + 16)]) ly S Hp W mem md [] ly S
    (remove Z.eq_dec (p - 16) Hp) _ 0 (p - 16) (n + 16) 0 (ew E' 2) (getr regs 1) ch HS (pal_free B PAL) eq_refl HJ2).
  - exact Hblk.
  - apply prh_hp_remove_notin.
  - rewrite Fa0, ?OLD by lia. rewrite Up. unfold w64. f_equal; lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E' _ ms3 2%bv HS).
  - reflexivity.
  - exact Usp'.
  - reflexivity.
  - lia.
  - rewrite WS, Has. lia.
  - rewrite Fgp, ?OLD by lia. rewrite E3. exact Hgp.
  - rewrite Ftp, ?OLD by lia. rewrite E4. exact Htp.
  - exact Fra'.
  - exact Hra.
  - exact HQM.
  - apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch); [| lia | exact Fs0' | lia].
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
    intros a Ha. exact (Kup a Ha).
  - exact HTRT.
  - intros _ i Hi. exists (p - 16, p - 16 + req_size (n + 16)). split; [left; reflexivity | cbn [fst snd]; lia]. }
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (b1 & b2 & Eab & Eab4) & Hfr4 & HPREc & Htrc &
  (q & trc & Hq & Hqin & Hpath & Hgf & Hleaf) & (K4a & K4b & K4c & _) & Hmn4).
(* ==== the post ==== *)
(* the journal is at the free's budget [call trace] (the rule's post, WS ++ [trace] at WS = []): the one trace this
   free can store, so wbudget [trace] 0 holds (YCbqGwild.wfresh_one_in) *)
unfold fpostb, YCbqGwild.apost_base_xbR.
exists ly4, S4, (remove Z.eq_dec (p - 16) Hp), regs4, mem4, md4, (0 + (st_nev S4 - st_nev S)),
  [call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms3) ch].
split; [reflexivity|].
split; [unfold YCbqGwild.wbudget; rewrite (ff_call_trace_eq ly _ (ms_regs ms3) regs ch Fsp' Fra'' Fs0');
  rewrite YCbqGwild.wfresh_one_in by (left; reflexivity); lia|].
split; [exact HJ4|].
split.
{ apply (aregs_preserved_trans regs (ms_regs ms3) regs4); [|exact HP4].
  eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS HAE'). vm_compute. reflexivity. }
split.
{ change S4 with (snd (tt, S4)).
  eapply (YGcfRoomLive.RL_free_step SEGS B); [eapply acall_pre_x_xs_cf; exact HPREc |
    exact (CfRoomLivePreset.preset_rl_b24_ok S HC24) | exact HRL | exact Hpath]. }
split; [reflexivity|].
split; [exists b1, b2; split; [exact Eab | exact Eab4]|].
assert (Hqn : q <> PNull) by (intros ->; unfold sptr_addr in Hq; cbn in Hq; lia).
split.
{ (* the run position, HFr: h-pre-b1's room_pos_keep_free at the tail call *)
  intros sm x os i H0 hist Hpos He. eexists.
  exact (PresetRoomPosKeep.room_pos_keep_free SEGS B ly S _ W _ _ _ ch sm x os i H0 hist q (n + 16) _ trc S4
    (acall_pre_x_xs_cf SEGS B ly S _ W _ _ _ ch HPREc) HTRT Hqin Hqn Hpath Hpos He). }
split.
{ (* the run position, HBulk: h-pre-b1's room_pos_keep_bulk_free at the tail call *)
  intros sm x os i L k H0 hb He Hk Hpos. eexists.
  exact (PresetRoomPosKeep.room_pos_keep_bulk_free SEGS B ly S _ W _ _ _ ch sm x os i L k H0 hb q (n + 16) _ trc S4
    (acall_pre_x_xs_cf SEGS B ly S _ W _ _ _ ch HPREc) HTRT Hqin Hqn Hpath He Hk Hpos). }
(* the class-24 live count loses exactly this block's request (S1Ccnt24.v's prh_ccnt24_free) *)
split; [exact (prh_ccnt24_free B ly S ly4 S4 b1 b2 (p - 16, n + 16) Eab Eab4) |].
(* the hull meters: the free keeps both (YGcfSecsStep.secs_free_step on the free's model path) *)
split; [exact (PresetHullBudget.hull_used_same S S4 [] (YGcfSecsStep.secs_free_step _ _ _ _ _ Hpath)) |].
(* the memnorm keep: the runners' carrier to the tail call's memory, then the free's own keep *)
split; [intros H0; exact (Hmn4 (HPM H0)) |].
exists l1, l2. split; [exact ELam|].
(* the statics but g_live, and the other heads, are the entry's *)
assert (Kst : forall a, Exists (in_zr a) prh_pst -> ~ (pi_g_live <= a < pi_g_live + 8) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hng. pose proof (ff_pst_range a Ha) as Hr. destruct (pal_pst_ok a Ha) as [Ho He].
  rewrite (K4c a (pst_in_img_B a Ha) Ho He).
  rewrite (KB a ltac:(unfold SHADOW_OFF in Hr; lia) ltac:(unfold SHADOW_OFF in Hr; lia) Hng).
  rewrite (Hkeep a ltac:(unfold SHADOW_OFF in Hr; lia) ltac:(unfold SHADOW_OFF in Hr; lia)
    ltac:(unfold shadow_addr; pose proof (Z.div_pos (p - 16) 8 ltac:(lia) ltac:(lia)); lia)).
  apply KA; [unfold SHADOW_OFF in Hr; lia | unfold SHADOW_OFF in Hr; lia | exact Hng]. }
assert (Khd : forall a ka i, In (a, ka) (l1 ++ l2) -> 0 <= i < 8 ->
  aview SEGS (w_H W4) mem4 (a - 16 + i) = aview SEGS (w_H W) mem (a - 16 + i)).
{ intros a ka i Ha Hi. pose proof (Hnp a ka Ha) as Hne.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HL (Hsub a ka Ha)) as (Hka & Hbla & _ & Ha16 & _).
  rewrite Hcf in Hbla.
  destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md (a - 16) (ka + 16) HAR Hbla) as (_ & Ha4096 & Haceil & Haapp & _).
  assert (Hreqa : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
  rewrite Hreqa in Haceil, Haapp.
  assert (Hdj : zdisjoint (a - 16, req_size (ka + 16)) (p - 16, req_size (n + 16))).
  { apply (sep_blocks_x SEGS B ARcfx LAWS ly S Hp W mem md); [exact HAR | exact Hbla | exact Hblk |].
    intros Heq. injection Heq as Heq _. apply Hne. lia. }
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Hreqa, Hreq in Hdj.
  pose proof (in_app_addr _ _ (a - 16 + i) Haapp ltac:(lia)) as Happa.
  assert (Hnimg : ~ (pi_g_live <= a - 16 + i < pi_g_live + 8)).
  { intros Hg. apply (ff_blk_not_img ly S Hp W mem md (a - 16) (ka + 16) (a - 16 + i) HAR Hbla); [rewrite Hreqa; lia|].
    apply pst_in_img_B. apply ff_live_pst. lia. }
  rewrite (K4b (a - 16) (ka + 16) i Hbla ltac:(rewrite Hreqa; lia) ltac:(cbv beta; rewrite Hreq; lia)).
  rewrite (KB (a - 16 + i) ltac:(lia) ltac:(lia) Hnimg).
  rewrite (Hkeep (a - 16 + i) ltac:(lia) ltac:(lia) (ff_shadow_app (p - 16) (a - 16 + i) Hpc Happa)).
  apply KA; [lia | lia | exact Hnimg]. }
apply (prh_ledger_disown B ly S Hp W mem ly4 S4 (remove Z.eq_dec (p - 16) Hp) W4 mem4 l1 l2 p n peak cnt fail ran
  peak cnt fail ran most own).
- rewrite <- ELam. exact HL.
- apply (prh_glob_final_le W mem W4 mem4 (Ledger.lsum Lam) peak cnt fail ran (Ledger.lsum (l1 ++ l2)) cnt fail ran most own HGl).
  + apply (prh_val_mem_keep _ _ _ _ _ Hlive3). intros k Hk. apply (mbyte_of_aview SEGS).
    apply K4c; [apply pst_in_img_B; apply prh_pst_live; exact Hk | exact (proj1 (pal_pst_ok _ (prh_pst_live k Hk))) |
      exact (proj2 (pal_pst_ok _ (prh_pst_live k Hk)))].
  + lia.
  + apply (prh_val_mem_keep _ _ _ _ _ Gpeak). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_peak; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
  + apply (prh_val_mem_keep _ _ _ _ _ Gcnt). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_count; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
  + lia.
  + apply (prh_val_mem_keep _ _ _ _ _ Gfail). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_fail; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
  + lia.
  + apply (prh_val_mem_keep _ _ _ _ _ Gran). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_ran; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
  + exact Rran.
  + destruct Gmost as [Gm Gmb]. split; [|exact Gmb].
    apply (prh_val_mem_keep _ _ _ _ _ Gm). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_most; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
  + destruct Gown as [Go Gob]. split; [|exact Gob].
    apply (prh_val_mem_keep _ _ _ _ _ Go). intros k Hk. apply (mbyte_of_aview SEGS). apply Kst; [apply prh_pst_own; exact Hk|].
    revert Hk. ff_lits. intros Hk. lia.
- intros a ka i Ha Hi. rewrite ?Hcf. apply (mbyte_of_aview SEGS). exact (Khd a ka i Ha Hi).
- intros a ka Ha Hbl. rewrite ?Hcf in Hbl |- *. rewrite Eab in Hbl. rewrite Eab4.
  apply in_app_or in Hbl as [Hbl|[Heq|Hbl]]; [apply in_or_app; left; exact Hbl | | apply in_or_app; right; exact Hbl].
  exfalso. injection Heq as Heq _. apply (Hnp a ka Ha). lia.
- reflexivity.
Qed.

(* The fuzz_free text at image B, its whole-program listing, preset's CfParams and the allocator relation ARcfx *)
Theorem fuzz_free_holds_B :
  tfuzz_free_specX (cp := CfParams_preset) (PI := prh_img_B) (RL := prh_room_live_a8) (L := B_prog_listing)
    (PA := PI_prog_B) B ARcfx SK.
Proof.
unfold tfuzz_free_specX, fpre, fpostbm, fQmn.
intros most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran [HPRE HRO] HRL HC24 HHUL Htr H10 Hpn HL.
destruct (Z.eq_dec p 0) as [->|Hp0].
- (* p = 0: S' = S keeps the room, the run position, the class-24 bound and both hull meters; the plain walk (no
     free), lifted to wle' segs RZ_cf *)
  cbn [Z.eqb].
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf));
    [exact (SRr_SRr' SEGS YGcfRehidePost.RZ_cf _ _ _ (ff_p0 ly S Hp W regs mem md ch Lam peak cnt fail ran most own HPRE H10 HL))|].
  (* a NULL free stores nothing: its post is the budgeted one at WS = [] (YCbqGwild.apost_base_xb_of_xR at wle', after
     YCbqG.apost_base_x_R_lift at YA0nH.wle_wle') *)
  intros W' c' _ H. unfold fpostb.
  apply (YCbqGwild.apost_base_xb_of_xR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS YGcfRehidePost.RZ_cf));
    [exact (le_n 0)|].
  apply (apost_base_x_R_lift (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS YGcfRehidePost.RZ_cf)
    (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
  eapply ff_fpost_mono; [|exact H]. cbv beta.
  intros ly' S' Hp' W'' regs' mem' md' (-> & HHp & Hab & HL' & Hmn). split; [|exact Hmn].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl)|].
  split; [exact (PresetHullBudget.hull_used_refl S [])|].
  (* K1's post-implication at E = []: the position is kept (S' = S) *)
  split; [intros _ sm x os i H0 hist Hpos _; exists hist; cbn [length]; rewrite Nat.add_0_r; exact Hpos|].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl)|].
  split; [intros Hc0; exfalso; exact (Hc0 eq_refl)|].
  split; [intros Hb; exact Hb|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [exact HHp|]. split; [exact Hab | exact HL'].
- destruct Hpn as [Hp0' | Hin]; [contradiction|].
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0).
  eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf));
    [exact (ff_nz ly S Hp W regs mem md ch p n Lam peak cnt fail ran most own HPRE (HRL Hp0) (HC24 Hp0) (HHUL Hp0)
       (proj1 HRO) Htr H10 Hin HL)|].
  intros W' c' _ H. eapply ff_fpostb_mono; [|exact H]. cbv beta.
  intros ly' S' Hp' W'' regs' mem' md' (HR & HHp & Hab & HRP & HRB & Hc24 & HU & Hmn & HL').
  split.
  { split; [intros _; exact HR|].
    split; [exact HU|].
    split; [intros Hc0; contradiction|].
    (* K1's post-implications at E = [HFr (n + cf_head)] and at the bulk event: prh_run_at_one gives the run's event *)
    split; [intros _ sm x os i H0 hist Hpos He; apply prh_run_at_one in He;
            destruct (HRP sm x os i H0 hist Hpos He) as [h' Hh']; exists h'; cbn [length]; rewrite Nat.add_1_r; exact Hh'|].
    split; [intros _ sm x os i H0 L kL hb Hb He Hk; apply prh_run_at_one in He; exact (HRB sm x os i L kL H0 hb He Hk Hb)|].
    split; [intros Hb24; lia|].
    right. split; [exact Hp0|]. split; [exact HHp|]. split; [exact Hc24|]. split; [exact Hab | exact HL']. }
  (* the keep across the free (fQmn of the text's fpostbm, PRH_Base.v): ff_nz's *)
  exact Hmn.
Qed.

End f.
End d.
