(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths and module names changed; 206 of its 320 lines of code are new or changed and 73 lines of the source are left out. *)
(* reac_ctrl_scene_set_mac (fuzz_scene.asan-ubsan 0x83e04, 21 words: 20 instructions and the trap
   word): the contract of the asan-ubsan build's code and its walk. The function takes a 16-byte
   frame on the machine stack at entry and saves ra there on every path. It returns -1 when a1 (n)
   is not 8904, or a0 (body) is 0, or a2 (mac) is 0. Else it traps (unimp) when body + 832 wraps
   past 2 ^ 64, and otherwise calls __asan_memcpy (body + 832, mac, 6) and returns 0: the 6 bytes at
   body + 832 read as the 6 bytes at mac afterwards. Under the contract's premises the trap is not
   reached: body + 838 lies in a live block, below alloc_ceiling.

   The numerals, each from the pinned image
   pau-pipeline/libreac/bin/fuzz_scene/fuzz_scene.asan-ubsan
   (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f; the unstripped twin
   unstripped/fuzz_scene/fuzz_scene.asan-ubsan, sha256 ef0b41158fe08b45b5a8a0e514f8ebc31f2960d2b90acc03576a682fae2baf33,
   holds the same 21 words at 0x83e04 and gives the symbols):
   - the function: .symtab reac_ctrl_scene_set_mac = 0x83e04, size 84 = 21 words (the last, 0x83e54,
     is the trap word 0xc0001073). Its offset AF_reac_ctrl_scene_set_mac comes from lib/AU/Prog/SceneList.v
     and is not restated here.
   - 16 (SET_MAC_FRAME, stack_region 16, the walk's -16): addi sp,sp,-16 at 0x83e04 (word
     0xff010113); sd ra,8(sp) at 0x83e08 (0x00113423); ld ra,8(sp) at 0x83e48 (0x00813083);
     addi sp,sp,16 at 0x83e4c (0x01010113).
   - 8904 (SCENE_BYTES = 0x22c8): lui a2,0x2 at 0x83e10 (0x00002637) and addiw a4,a2,712 at
     0x83e14 (0x2c86071b), 0x2000 + 0x2c8; bne a1,a4 at 0x83e1c (0x02e59463) compares it with n.
   - 0 tests of body and mac: beqz a0 at 0x83e20 (0x02050263), beqz a3 at 0x83e24 (0x02068063;
     a3 = mac by mv a3,a2 at 0x83e0c, 0x00060693). All three refusals go to 0x83e44.
   - -1: li a2,-1 at 0x83e18 (0xfff00613), moved to a0 by mv a0,a2 at 0x83e44 (0x00060513).
     0: li a2,0 at 0x83e40 (0x00000613), moved by the same mv.
   - -832 (the UBSan wrap guard of body + 832): li a1,-832 at 0x83e28 (0xcc000593); bgeu a0,a1 at
     0x83e2c (0x02b57463) goes to the trap word at 0x83e54 (0xc0001073, unimp).
   - 832 (MAC_OFF): addi a0,a0,832 at 0x83e30 (0x34050513).
   - 6 (MAC_LEN): li a2,6 at 0x83e34 (0x00600613); a1 = mac by mv a1,a3 at 0x83e38 (0x00068593).
   - the callee: jal 0x539f0 at 0x83e3c (0xbb5cf0ef); .symtab __asan_memcpy = 0x539f0 (size 1180),
     the listing's SS___asan_memcpy (lib/AU/Prog/SceneList.v, the slot after 0x68593).
   The other constants are not image numerals: ESTACK (4096, Reusable/YG0d.v) is the runtime's
   stack window; the stack-pointer fact (2 ^ 46, 2 ^ 47, alignment 2 ^ 4) comes from astk_ok and
   asan_consts (lib/AU/YCbq.v); the shadow base and span are SHADOW_OFF and kHighShadowEnd
   (Reusable/YG0f.v); 2 ^ 32, 2 ^ 63, 2 ^ 64 are word bounds. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* REAC_SCENE_BYTES, the one length the function accepts (0x83e10, 0x83e14, 0x83e1c). *)
Definition SCENE_BYTES : Z := 8904.
(* REAC_SCENE_MAC_OFF, where the copy writes (0x83e30). *)
Definition MAC_OFF : Z := 832.
(* The copy's length (0x83e34). *)
Definition MAC_LEN : Z := 6.
(* The function's own frame (0x83e04). *)
Definition SET_MAC_FRAME : Z := 16.
(* The three tests the code makes before the copy, in the order of 0x83e1c, 0x83e20, 0x83e24:
   n is 8904, body is not 0, mac is not 0. *)
Definition scene_go (p n q : Z) : bool := ((n =? SCENE_BYTES) && negb (p =? 0) && negb (q =? 0))%bool.
(* The bytes outside the stack the code may write: the 6 bytes at body + 832, when it copies. *)
Definition setmac_fp (p n q : Z) : list (Z * Z) :=
if scene_go p n q then [(p + MAC_OFF, p + MAC_OFF + MAC_LEN)] else [].
Local Ltac zbool :=
repeat match goal with
| H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
| H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
end.
(* Turn the branch conditions of the path into facts on p, n, q, the values of a0, a1, a2 at entry. *)
Local Ltac sm_branch_facts E E10 E11 E12 Hp Hn Hq :=
repeat match goal with
| H : branch_taken _ (sv_denot E _) (sv_denot E _) = _ |- _ =>
first [rewrite branch_ne_U in H | rewrite branch_eq_U in H];
rewrite ?(U_atom E 10 _ E10 Hp), ?(U_atom E 11 _ E11 Hn), ?(U_atom E 12 _ E12 Hq) in H;
rewrite ?U_lit in H by lia
end.
Local Ltac sm_go_bool E E10 E11 E12 Hp Hn Hq p n q :=
unfold scene_go, SCENE_BYTES;
sm_branch_facts E E10 E11 E12 Hp Hn Hq; zbool;
destruct (Z.eqb_spec n 8904); destruct (Z.eqb_spec p 0); destruct (Z.eqb_spec q 0);
cbn [andb negb]; first [reflexivity | exfalso; lia].
(* The return value: a word given as a literal equals w64 of the same number modulo 2 ^ 64. *)
Local Ltac sm_w64 :=
first [ reflexivity | unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity ].
(* The UBSan guard at 0x83e2c (bgeu a0,a1 with a1 = -832, i.e. 2 ^ 64 - 832): when it is taken,
   body >= 2 ^ 64 - 832, which the block bound body + 838 <= alloc_ceiling contradicts. *)
Local Ltac sm_trap_false E E10 Hp :=
lazymatch goal with H : branch_taken BC_GEU (sv_denot E (SOff 10 0)) (sv_denot E _) = true |- _ =>
exfalso; rewrite branch_geu_U, (U_atom E 10 _ E10 Hp) in H;
first [rewrite U_lit in H by lia | rewrite U_SLit in H; unfold zcanon, M64 in H];
apply (proj1 (Bool.negb_true_iff _)) in H; apply Z.ltb_ge in H; lia
end.
(* The memory outside the frame [sp - 16, sp) is untouched by a run: its one region, the frame,
   is the only writable window. HM carries the fact from entry to the current state. *)
Local Ltac upd_mem_fr regs0 mem0 Usp :=
repeat match goal with
| H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
| H : mem_grows _ _ |- _ => clear H
end;
lazymatch goal with
| HF : frame_of _ ?rs ?m1 ?m2, HM : forall x : word, _ -> ?m1 x = mem0 x |- _ =>
let HM' := fresh "HM" in
assert (HM' : forall x : word, ~ (spZ regs0 - SET_MAC_FRAME <= bv_unsigned x < spZ regs0) -> m2 x = mem0 x)
by (intros x Hx; transitivity (m1 x); [|exact (HM x Hx)]; apply HF;
let rs' := eval vm_compute in rs in change rs with rs';
intros (r & [<- | []] & Hr);
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp in Hr; unfold SET_MAC_FRAME in Hx; lia);
clear HM HF; rename HM' into HM
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 16-byte frame
   and ESTACK below it for __asan_memcpy. *)
Definition A_reac_ctrl_scene_set_macP : Z := BASE + AF_reac_ctrl_scene_set_mac.
Definition SET_MAC_STK : Z := SET_MAC_FRAME + ESTACK.
Definition SB_SM : Z := SHADOW_OFF.
Definition Bx_SM : sv := SLit SB_SM.
Definition Bspan_SM : Z * Z := (SB_SM, kHighShadowEnd - 1).
Definition ss_sm : sstate :=
mkSS AF_reac_ctrl_scene_set_mac sr_atoms [stack_region SET_MAC_FRAME] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma sm_aview_same_at : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.
Section h.
Variable B : asyms.
(* What the code does. On every path: the frame is released, the callee-saved registers and the
   world are kept, and the journal holds with setmac_fp as the only bytes of the caller's blocks
   it may change (the 6 bytes at body + 832 when it copies, none on a refusal). a0 is 0 when the
   three tests pass and -1 else.
   When they pass: the 6 bytes at body + 832 read as the 6 bytes that were at mac, and every byte
   outside them and outside the stack the function uses ([sp - 16 - ESTACK, sp)) reads as before.
   When they fail: only the frame [sp - 16, sp) is written (ra at sp - 8), so every other byte of
   memory is the same. *)
Definition treac_ctrl_scene_set_mac_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (p n q : Z)
: world SEGS -> config -> Prop :=
apost_base (SK := SK) SEGS B SET_MAC_STK (setmac_fp p n q) regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
getr regs' 10 = w64 (if scene_go p n q then 0 else -1) /\
if scene_go p n q then
(forall i, 0 <= i < MAC_LEN -> aview SEGS (w_H W') mem' (p + MAC_OFF + i) = aview SEGS (w_H W) mem (q + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (p + MAC_OFF <= a < p + MAC_OFF + MAC_LEN) -> ~ (spZ regs - SET_MAC_STK <= a < spZ regs) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
else
(forall x : word, ~ (spZ regs - SET_MAC_FRAME <= bv_unsigned x < spZ regs) -> mem' x = mem x)).
(* p, n, q are body, n, mac. The premises on memory are needed only when the code reaches the copy:
   the 6 bytes at body + 832 lie in a live block of the caller (the copy writes them), the 6 bytes at
   mac lie in a live block or are a live frame object of the caller (the copy reads them), and the
   two ranges do not overlap (__asan_memcpy reports an overlap). *)
Definition treac_ctrl_scene_set_mac_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p n q : Z),
afn_pre SEGS B SET_MAC_STK ly S W regs mem md ch ->
getr regs 10 = w64 p -> getr regs 11 = w64 n -> getr regs 12 = w64 q ->
0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
(scene_go p n q = true ->
(exists b m, In (b, m) (ablocks B ly S) /\ b <= p + MAC_OFF /\ p + MAC_OFF + MAC_LEN <= b + req_size m) /\
((exists b m, In (b, m) (ablocks B ly S) /\ b <= q /\ q + MAC_LEN <= b + req_size m) \/
afobj SEGS B ly S W mem q MAC_LEN) /\
(p + MAC_OFF + MAC_LEN <= q \/ q + MAC_LEN <= p + MAC_OFF)) ->
SRr SEGS W (cfg_at SEGS A_reac_ctrl_scene_set_macP regs mem md) (treac_ctrl_scene_set_mac_post regs ly S W mem md p n q).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Let RUN := paj_run (SK := SK) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_scene) (PI := PI).
Lemma sm_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B SET_MAC_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_sm
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_set_mac)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_SM [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SET_MAC_STK = 4112) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold ss_sm. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, SET_MAC_FRAME. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.
Theorem pb_reac_ctrl_scene_set_mac : treac_ctrl_scene_set_mac_spec.
Proof.
unfold treac_ctrl_scene_set_mac_spec.
intros ly S W regs mem md ch p n q HPRE H10 H11 H12 Hp Hn Hq HGO.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (sm_entry ly S W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_init (SK := SK) SEGS B SET_MAC_STK (setmac_fp p n q) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SET_MAC_STK = 4112) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF16 : SET_MAC_FRAME = 16) by reflexivity.
assert (Hmo : MAC_OFF = 832) by reflexivity. assert (Hml : MAC_LEN = 6) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (HM : forall x : word, ~ (spZ regs - SET_MAC_FRAME <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
unfold cfg_at, A_reac_ctrl_scene_set_macP.
change (w64 (BASE + AF_reac_ctrl_scene_set_mac)) with (Z_to_bv 64 (BASE + AF_reac_ctrl_scene_set_mac)).
(* A refusal: the run through mv a0,a2 (0x83e44), ld ra, addi sp, ret, and the post with a0 = -1
   and only the frame written. *)
let refuse := idtac;
paj_run_tok RUN HS HJ SHOK Bspan_SM; [awr_ok_tac; exact Usp |];
upd_mem_fr regs mem Usp;
assert (Hgo : scene_go p n q = false) by (sm_go_bool E E10 E11 E12 Hp Hn Hq p n q);
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_ctrl_scene_set_mac_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
rewrite Hgo; cbv iota; split; [rewrite R10; sm_w64 | exact HM]
end in
(* One run up to the next branch. *)
let step := idtac;
paj_run_tok RUN HS HJ SHOK Bspan_SM; [awr_ok_tac; exact Usp |];
upd_mem_fr regs mem Usp in
(* The frame, the save of ra, the argument moves, then the tests of n (0x83e1c), body (0x83e20)
   and mac (0x83e24); each taken branch goes to the shared epilogue at 0x83e44. *)
step; psrr_branch_tok RUN BR HS SHOK Bspan_SM;
[ refuse
| step; psrr_branch_tok RUN BR HS SHOK Bspan_SM;
[ refuse
| step; psrr_branch_tok RUN BR HS SHOK Bspan_SM; [ refuse | idtac ] ] ].
(* The three tests passed: the premises on body and mac hold. *)
assert (Hgo : scene_go p n q = true) by (sm_go_bool E E10 E11 E12 Hp Hn Hq p n q).
destruct (HGO Hgo) as ((bd & bm & Hind & Hbd1 & Hbd2) & Hsrc & Hdisj).
destruct (al_blocks _ _ LAWS ly S W mem md bd bm HAR Hind) as (_ & Hbd4096 & Hbdceil & Hbdapp & _ & _ & _).
assert (HQB : 4096 <= q /\ q + MAC_LEN <= alloc_ceiling).
{ destruct Hsrc as [(sb & sm & Hins & Hsb1 & Hsb2) | ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _)].
- destruct (al_blocks _ _ LAWS ly S W mem md sb sm HAR Hins) as (_ & Hq4 & Hqc & _). lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hq4 & Hqc & _). lia. }
assert (HFPe : setmac_fp p n q = [(p + MAC_OFF, p + MAC_OFF + MAC_LEN)]) by (unfold setmac_fp; rewrite Hgo; reflexivity).
assert (HFPs : forall x, inFP (setmac_fp p n q) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ rewrite HFPe. intros x (r & [<- | []] & Hr). cbn [fst snd] in Hr. zlia. }
(* The UBSan guard: li a1,-832 (0x83e28), then bgeu a0,a1 (0x83e2c) to the trap word at 0x83e54.
   The taken branch is refuted from the block bound of body + 832. *)
paj_run_tok RUN HS HJ SHOK Bspan_SM; [awr_ok_tac; exact Usp |].
upd_mem_fr regs mem Usp.
psrr_branch_tok RUN BR HS SHOK Bspan_SM; [ sm_trap_false E E10 Hp | idtac ].
(* The arguments of the copy, up to the call of __asan_memcpy at 0x83e3c. *)
paj_run_tok RUN HS HJ SHOK Bspan_SM; [awr_ok_tac; exact Usp |].
upd_mem_fr regs mem Usp.
rename HM into HMT.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -16) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity)
end.
(* The copy: it writes [body + 832, body + 838) with the 6 bytes at mac and keeps every other byte
   above its own stack. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at (SK := SK) SEGS B LAWS Hsegs OCpy (SIGMA SS___asan_memcpy) AMEMCPY W rg mm
SET_MAC_STK (spZ regs) (setmac_fp p n q) ly S W mem md [] ly S _ 0 (p + MAC_OFF) q MAC_LEN (-16) _ HJ);
[ rewrite Ra0, E10, unsigned_lit_small by lia; reflexivity
| rewrite Ra1, E12; reflexivity
| rewrite Ra2; reflexivity
| lia
| lia
| lia
| exact Qsp
| reflexivity
| lia
| rewrite WS, Hes; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| intros a Ha; split;
[ right; left; split; [rewrite HFPe|];
[ exists (p + MAC_OFF, p + MAC_OFF + MAC_LEN); split; [left; reflexivity | cbn [fst snd]; lia]
| exists bd, bm; split; [exact Hind | lia] ]
| rewrite Hes; lia ]
| eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hind); lia
| eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hind); lia
| intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hind); lia
| cbv iota; destruct Hsrc as [(sb & sm & Hins & Hsb1 & Hsb2) | ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hq8 & HRA)];
[ (* mac in a live block *)
destruct (al_blocks _ _ LAWS ly S W mm _ sb sm (proj1 HJ) Hins) as (_ & _ & Hsc & _ & Hspres & _);
split; [lia|]; split; [lia|]; split;
[ intros a Ha; split;
[ apply (aview_some_of_apresent SEGS); apply (proj1 (Hspres a ltac:(lia)))
| rewrite Qsp, Hes; lia ] |];
split; [exact Hdisj|]; split;
[ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hins); lia |]; split;
[ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hins); lia |];
intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hins); lia
| (* mac a live frame object *)
destruct (frames_bounds SEGS B LAWS ly S W mm _ cid pos (proj1 HJ) Hfin) as (Hf4 & Hfc & Hfapp);
destruct (al_frames _ _ LAWS ly S W mm _ cid pos (proj1 HJ) Hfin) as (_ & _ & Hfpres & _);
split; [lia|]; split; [lia|]; split;
[ intros a Ha; split;
[ apply (aview_some_of_apresent SEGS); apply (proj1 (Hfpres a ltac:(lia)))
| rewrite Qsp, Hes; lia ] |];
split; [exact Hdisj|]; split; [zlia |]; split;
[ eapply (range_addressable_entry_frame (SK := SK) SEGS B LAWS);
[ exact HJ | exact Hfin | exact Hcid | exact Hflo | exact Hfhi | exact Hfal | exact HFPs | exact HAR | exact HRA ] |];
intros _; eapply (shadow_hull_vis_of_frame SEGS B LAWS ly S W mm _ cid pos q MAC_LEN (proj1 HJ) Hfin); lia ] ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* Back at the return slot: the frame (the saved ra) is kept by the copy. *)
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall k, (k < 32)%nat -> ew E' k = ew E k) by (intros k Hk; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk).
assert (HAE' : env_agree 32 (Ereg regs []) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK' : sh_ok SEGS Bx_SM [] E' (mrestrict (w_H W) mem2)) by constructor.
clear SHOK.
(* li a0,0, the reload of ra, the release of the frame and the return. *)
paj_run_tok RUN HS HJ2 SHOK' Bspan_SM; [awr_ok_tac; exact Usp' |].
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HF : frame_of _ ?rs mem2 (ms_mem ?msc) |- _ =>
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
assert (HK : forall x : word, ~ (spZ regs - SET_MAC_FRAME <= bv_unsigned x < spZ regs) -> ms_mem msc x = mem2 x)
by (intros x Hx; apply HF; let rs' := eval vm_compute in rs in change rs with rs';
intros (r & [<- | []] & Hr); cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Usp' in Hr; lia);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_ctrl_scene_set_mac_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
split; [apply (ajournal_materialize (SK := SK) SEGS B LAWS Hsegs); exact HJ2|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E' _ _ regs [] HS); [exact HAE' | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
rewrite Hgo; cbv iota; split; [rewrite R10; sm_w64|]; split;
[ intros i Hi;
rewrite (sm_aview_same_at (w_H W) mem2 (ms_mem msc) (p + MAC_OFF + i)) by (apply HK; rewrite unsigned_lit_small by lia; lia);
rewrite (Heff i Hi);
cbv iota;
apply sm_aview_same_at; apply HMT; rewrite unsigned_lit_small by lia; lia
| intros a Ha Hnd Hns;
rewrite (sm_aview_same_at (w_H W) mem2 (ms_mem msc) a) by (apply HK; rewrite unsigned_lit_small by lia; lia);
rewrite (Hfr a Ha Hnd) by (rewrite Hes; lia);
apply sm_aview_same_at; apply HMT; rewrite unsigned_lit_small by lia; lia ]
end.
Qed.
End h.
End f.
End d.
