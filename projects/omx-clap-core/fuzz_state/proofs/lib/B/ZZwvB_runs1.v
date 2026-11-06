(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_runs1.v (a working branch
   1a5dc5b2e7c): same lemma names, every return address, frame slot and register re-measured on fs.asan-ubsan; the entry
   state is lib/B/FSW_write_value_entry.v's (wv_ss0 / wv_SH / wv_xs, with its wv_awr0 / wv_frame0), not a local copy;
   imports point at lib/B's image files and walk kit.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B. *)
(* write_value's CONTAINER arms (array / object), fs.asan-ubsan image B (write_value 0x84010, frame 192): the three
   ENGINE RUNS at the ends of the arms, between two call sites. No semantics, no function contract, no allocator
   reasoning: one token run each, then every fact the caller needs at the call.
   MEASURED with the engine on the pinned fs.asan-ubsan (a build machine, this lane's probe of these exact states):
   - the entry state wv_ss0 ty (ty = 5 / 6) runs to put (0x8449c) with ra = WVC_R_OPEN, a0 = the entry a0,
     a1 = '[' / '{', a2 = 1, sp = the entry sp - 192; s0 = a0, s1 = a1, s3 = a2 (s2 holds v >> 3); the frame's slots
     16 (v & 7, folded to 0), 24 (the entry a3 = d), 72 (the shadow base), 80 (shadow(v)) and 88 .. 184 (the thirteen
     saved registers); no fresh atom, no shadow obligation;
   - wvc_ssO ty with n = 0 TAIL-jumps to put (sp back up to the frame top spF, ra and the callee-saved registers
     reloaded from the frame, gp / tp untouched). Image B selects the separator (frame slot 56, a branch on pretty)
     BEFORE it tests n, so this run needs the pretty condition as well as n = 0;
   - wvc_ssO ty with n <> 0 runs to indent (0x86368) with ra = WVC_R_IND, a0 = s0, a1 = s3, a2 = d + 1 (d read back
     from the frame slot 24, xatom 4), writes the prelude slots 8 .. 64 (slot 32 = (0 <u pretty) + 1) and sets the loop
     registers s2, s4 .. s11. It meets the UBSan guard 0x8418c (`bnez s10`, s10 = slt (addiw d 1) d, the signed overflow
     of d + 1): the condition wvc_cSLT, proved from d + 1 < 2 ^ 31, rules it out.
   FRAME TOP vs JOURNAL TOP: write_value's frame is [spF - WVC_F, spF) below its entry sp spF; the caller's journal
   carries a RAISED top sp0 >= spF (the window top of the spec) and the stack bound STK, so the resumed runs take
   spF <= sp0 and sp0 - STK <= spF - WVC_F, and every call-site continuation also hands over gp / tp (regs 3, 4).
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= reading a run's end state ================= *)
Section V. Context {fx : YK11.FPState}.
Lemma wvr1_reg : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> YK11.getr (ms_regs ms) r = sv_denot E e.
Proof. intros H E ss ms r e HS He. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), He. reflexivity. Qed.
Lemma wvr1_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> YK11.getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS He. rewrite (wvr1_reg H E ss ms r _ HS He). apply fsw_SOff0. Qed.
Lemma wvr1_reg_same : forall (H : word -> bool) E ss ss' ms ms' (r : bv 5),
  st_ok tfibsegs E ss' (restrict H ms') -> st_ok tfibsegs E ss (restrict H ms) ->
  sr_get (ss_regs ss') r = sr_get (ss_regs ss) r -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r.
Proof.
intros H E ss ss' ms ms' r HS' HS He.
rewrite (st_ok_restrict_reg tfibsegs H E ss' ms' r HS'), (st_ok_restrict_reg tfibsegs H E ss ms r HS), He.
reflexivity.
Qed.
(* a chunk of a region read in one env at one base is a chunk of another env / base when the byte address and the
   denotation agree *)
Lemma wvr1_chunk_mv : forall E E' m b b' o o' (w : N) e e' cs,
  Forall (YP09.chunk_ok tfibsegs E m b) cs -> In (YP09.mkChunk o (CVal w e)) cs ->
  b + o = b' + o' -> sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E' m b' (YP09.mkChunk o' (CVal w e')).
Proof.
intros E E' m b b' o o' w e e' cs Hcs Hin Hb He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
intros i Hi. destruct (Hc i Hi) as (x & Hx & Hm). exists x.
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hx, Hm |- *.
rewrite <- He. replace (b' + o' + i) with (b + o + i) by lia. split; [exact Hx | exact Hm].
Qed.
(* the saved-register atoms of the resumed env *)
Lemma wvr1_xs_saved : forall R regs str kids keys n d ke key j,
  (j < 13)%nat ->
  ew (Ereg R (fs_extraT ++ wvc_xs regs str kids keys n d ke key)) (xatom (5 + j)) =
  YK11.getr regs (nth j wvc_saved 0%bv).
Proof.
intros R regs str kids keys n d ke key j Hj.
change (xatom (5 + j)) with (32 + (6 + j))%nat. rewrite ew_Ereg_extra.
do 13 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
(* the shadow base (atom 32) of an env whose extra atoms start with fs_extraT *)
Lemma wvr1_e32 : forall regs xs, ew (Ereg regs (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs xs. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
(* the arithmetic the container prelude does on the entry depth d (xatom 4, read back from the frame slot 24) *)
Lemma wvr1_w1 : forall E d, ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  U E (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) = d + 1.
Proof.
intros E d Ex4 Hd0 Hd1.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E (xatom 4) d Ex4) by lia. rewrite U_SLit.
change (zcanon 1) with 1. rewrite (Z.mod_small d) by lia. change (1 mod 2 ^ 32) with 1.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (d + 1 + 2 ^ 31) (2 ^ 32)) by lia.
replace (d + 1 + 2 ^ 31 - 2 ^ 31) with (d + 1) by lia. apply Z.mod_small. lia.
Qed.
Lemma wvr1_d1 : forall E d, ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) = Z_to_bv 64 (d + 1) /\
  sv_denot E (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)) = Z_to_bv 64 (d + 1).
Proof.
intros E d Ex4 Hd0 Hd1.
pose proof (wvr1_w1 E d Ex4 Hd0 Hd1) as U1.
split.
- apply bv_eq. rewrite (unsigned_lit_small (d + 1)) by lia. exact U1.
- apply bv_eq. rewrite (unsigned_lit_small (d + 1)) by lia.
  change (U E (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)) = d + 1).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U1, U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
  apply zcanon_id. unfold M64. lia.
Qed.
(* s10 = slt (addiw d 1) d, the signed-overflow flag of d + 1 that the guard 0x8418c tests, is 0 *)
Lemma wvr1_slt : forall E d, ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  U E (SAlu ALU_SLT (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SOff (xatom 4) 0)) = 0.
Proof.
intros E d Ex4 Hd0 Hd1.
rewrite U_SAlu, (wvr1_w1 E d Ex4 Hd0 Hd1), (U_atom E (xatom 4) d Ex4) by lia. cbn [zalu_raw].
rewrite (swrap64_id (d + 1)), (swrap64_id d) by (unfold half64; lia).
rewrite (proj2 (Z.ltb_ge (d + 1) d)) by lia. reflexivity.
Qed.
Lemma wvr1_slt_den : forall E d, ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  sv_denot E (SAlu ALU_SLT (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SOff (xatom 4) 0)) = Z_to_bv 64 0.
Proof. intros E d Ex4 Hd0 Hd1. rewrite denot_lit_U, (wvr1_slt E d Ex4 Hd0 Hd1). reflexivity. Qed.
Lemma wvr1_seplen : forall E p s, ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> s = wvc_seplen p ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) = sv_denot E (SLit s).
Proof.
intros E p s E19 Hp ->. apply bv_eq.
change (U E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 19 0)) (SLit 1)) = U E (SLit (wvc_seplen p))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 19 p E19 Hp), !U_SLit.
unfold wvc_seplen. change (zcanon 0) with 0. destruct (Z.eqb_spec p 0) as [->|Hn].
- vm_compute. reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 p)) by lia. vm_compute. reflexivity.
Qed.
End V.

(* ---- per-chunk and per-register steps on a run's end state ---- *)
Ltac wvr1_in := repeat (first [left; reflexivity | right]).
(* a chunk of the entry run's frame (base: the entry sp, env Ereg regs (fs_extraT ++ wv_xs ..)) as a chunk of wvc_cs0
   (base: the entry sp - WVC_F) in the resumed env Ereg R (fs_extraT ++ wvc_xs regs ..): slot 16 a literal, slot 24 the
   entry a3 (= d, HD) as xatom 4, slot 72 the shadow base, slot 80 shadow(v) at the entry a1 (atom 11) as shadow(v)
   at the resumed s1 (atom 9, HR9), slots 88 .. 184 the saved registers as xatom 5 .. 17 *)
Ltac wvr1_den0 HR9 HD :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = sv_denot _ (SLit _) => reflexivity
  | |- sv_denot _ (SAlu _ _ _) = sv_denot _ (SAlu _ _ _) =>
      cbn [sv_denot]; rewrite !wvr1_e32, (ew_Ereg_nat _ _ 11 11%bv eq_refl), (ew_Ereg_nat _ _ 9 9%bv eq_refl), HR9;
      reflexivity
  | |- sv_denot _ (SOff 13 0) = sv_denot _ (SOff _ 0) =>
      rewrite !fsw_SOff0, (ew_Ereg_nat _ _ 13 13%bv eq_refl), HD;
      change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity
  | |- sv_denot _ (SOff 32 0) = sv_denot _ (SOff 32 0) => rewrite !fsw_SOff0, !wvr1_e32; reflexivity
  | |- sv_denot _ (SOff _ 0) = sv_denot _ (SOff ?b 0) =>
      rewrite !fsw_SOff0;
      let j := eval vm_compute in (b - 38)%nat in
      change b with (xatom (5 + j)); rewrite (wvr1_xs_saved _ _ _ _ _ _ _ _ _ j) by lia;
      apply ew_Ereg_nat; vm_compute; reflexivity
  end.
Ltac wvr1_ck0 HCs HR9 HD :=
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o' _) =>
    let o := eval vm_compute in (o' - 192) in
    eapply (wvr1_chunk_mv _ _ _ _ _ o o' _ _ _ _ HCs); [wvr1_in | unfold WVC_F; lia | wvr1_den0 HR9 HD] end.
(* a chunk of the open run's frame as a chunk of wvc_csL p, same env, same base *)
Ltac wvr1_denL E19 Hsl :=
  lazymatch goal with
  | |- sv_denot _ (SAlu ALU_ADD (SAlu ALU_SLTU _ _) _) = sv_denot _ (SLit _) =>
      eapply (wvr1_seplen _ _ _ E19); [lia | symmetry; exact Hsl]
  | _ => reflexivity
  end.
Ltac wvr1_ckL HCs E19 Hsl :=
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o' _) =>
    let o := eval vm_compute in o' in
    eapply (wvr1_chunk_mv _ _ _ _ _ o o' _ _ _ _ HCs); [wvr1_in | lia | wvr1_denL E19 Hsl] end.
Ltac wvr1_lit HSf := apply (fsw_reg_lit _ _ _ _ _ _ HSf); [vm_compute; reflexivity | ].
Ltac wvr1_atom HSf := apply (wvr1_reg_atom _ _ _ _ _ _ HSf); vm_compute; reflexivity.
Ltac wvr1_sv HSf := apply (wvr1_reg _ _ _ _ _ _ HSf); vm_compute; reflexivity.
Ltac wvr1_pc HSf := etransitivity; [exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HSf eq_refl) | reflexivity].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ---- the write windows: a resumed run writes only the frame [spF - WVC_F, spF), which lies inside the caller's
   journal window [sp0 - STK, sp0) (the entry run's: FSW_write_value_entry.wv_awr0 / wv_frame0) ---- *)
Lemma wvr1_awrO : forall E ss ty STK sp0 spF FP bl0 blc lyc own fr0,
  ss_mem ss = ss_mem (wvc_ssO ty) -> bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E ss ty STK sp0 spF FP bl0 blc lyc own fr0 Hss E2 Hsp HSTK. rewrite Hss.
change (ss_mem (wvc_ssO ty)) with [fstk_ret WVC_F wvc_cs0; fs_got_region; fs_bcell_region 32; wvc_node ty].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spF - WVC_F - sp0);
  [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [wvc_node YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.
Lemma wvr1_frameO : forall E ss ty (m m' : word -> option byte) sp0,
  ss_mem ss = ss_mem (wvc_ssO ty) -> frame_of E (ss_mem ss) m m' -> bv_unsigned (ew E 2) = sp0 - WVC_F ->
  forall x : word, ~ (sp0 - WVC_F <= bv_unsigned x < sp0) -> m' x = m x.
Proof.
intros E ss ty m m' sp0 Hss HF E2 x Hx. apply HF. intros (r & Hin & Hr). rewrite Hss in Hin.
change (ss_mem (wvc_ssO ty)) with [fstk_ret WVC_F wvc_cs0; fs_got_region; fs_bcell_region 32; wvc_node ty] in Hin.
cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
  cbv [fstk_ret fs_got_region fs_bcell_region wvc_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  try (rewrite E2 in Hr); unfold WVC_F in *; lia.
Qed.

(* ================= (2) the entry run: to put of '[' / '{' ================= *)
(* No UBSan guard of the arms is on this run (0x8404c / 0x84060 on the root node are the entry's, ruled out by
   wv_gf's node fact, FSW_write_value_entry.wv_entry). *)
Lemma wvc_seg_entry : forall (W : world tfibsegs) ms mdc regs ty slo shi str kids keys n d STK ot FP ly S W0 mem md
    own lyc Sc U k (Q : world tfibsegs -> config -> Prop),
  wvc_at B (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (wv_ss0 ty slo shi) wv_SH W ms
    (STK + (ot - spZ regs)) ot FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  spZ regs <= ot -> WVC_F <= STK ->
  YK11.getr regs 13%bv = w64 d -> 0 <= d < 2 ^ 64 ->
  (forall ms' mdc',
     ajournal tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spZ regs - WVC_F <= bv_unsigned x < spZ regs) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     (forall R ke key, YK11.getr R 9%bv = YK11.getr regs 11%bv ->
        Forall (YP09.chunk_ok tfibsegs (Ereg R (fs_extraT ++ wvc_xs regs str kids keys n d ke key))
                  (mrestrict (w_H W) (ms_mem ms')) (spZ regs - WVC_F)) wvc_cs0) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_OPEN ->
     YK11.getr (ms_regs ms') 10%bv = YK11.getr regs 10%bv ->
     YK11.getr (ms_regs ms') 11%bv = w64 (wvc_open ty) ->
     YK11.getr (ms_regs ms') 12%bv = w64 1 ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 (spZ regs - WVC_F) ->
     YK11.getr (ms_regs ms') 8%bv = YK11.getr regs 10%bv ->
     YK11.getr (ms_regs ms') 9%bv = YK11.getr regs 11%bv ->
     YK11.getr (ms_regs ms') 19%bv = YK11.getr regs 12%bv ->
     (forall r, In r [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> YK11.getr (ms_regs ms') r = YK11.getr regs r) ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc regs ty slo shi str kids keys n d STK ot FP ly S W0 mem md own lyc Sc U k Q
  (HS & SHOK & HJ & HARU) Hty Hot HSTK HD Hd HK.
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
destruct Hty as [-> | ->].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan A_put.
all: lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => apply wv_awr0; [exact E2 | exact Hot | exact HSTK]
  | HSf : st_ok _ _ _ (restrict _ ?m), HFr : frame_of _ (ss_mem (wv_ss0 ?t ?l ?h)) (mrestrict _ _) (mrestrict _ _)
    |- SRr _ _ (mkCfg ?m _) _ =>
      pose proof (fsw_region_nth _ _ _ 0 _ HSf eq_refl) as HR0;
      destruct HR0 as (_ & _ & _ & HCs);
      cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HCs; rewrite E2 in HCs;
      eapply HK;
      [ exact HJ
      | exact HARU
      | intros x Hx; eapply wv_frame0; [exact HFr | exact E2 | exact Hx]
      | let R := fresh "R" in let ke := fresh "ke" in let key := fresh "key" in let HR9 := fresh "HR9" in
        intros R ke key HR9;
        lazymatch goal with |- Forall ?P ?l0 => let l1 := eval vm_compute in l0 in change (Forall P l1) end;
        repeat (apply Forall_cons; [wvr1_ck0 HCs HR9 HD |]); apply Forall_nil
      | wvr1_lit HSf; unfold WVC_R_OPEN; lia
      | rewrite (wvr1_reg_atom _ _ _ _ 10%bv 10%nat HSf) by (vm_compute; reflexivity);
        exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)
      | wvr1_lit HSf; unfold wvc_open, WVC_LBRACE, WVC_LBRACKET; cbn; lia
      | wvr1_lit HSf; lia
      | rewrite (wvr1_reg _ _ _ _ 2%bv (SOff 2 (-192)) HSf) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite E2; unfold WVC_F; f_equal; lia
      | rewrite (wvr1_reg_atom _ _ _ _ 8%bv 10%nat HSf) by (vm_compute; reflexivity);
        exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)
      | rewrite (wvr1_reg_atom _ _ _ _ 9%bv 11%nat HSf) by (vm_compute; reflexivity);
        exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)
      | rewrite (wvr1_reg_atom _ _ _ _ 19%bv 12%nat HSf) by (vm_compute; reflexivity);
        exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)
      | let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
        lazymatch goal with |- YK11.getr _ ?q = _ =>
          let nq := eval vm_compute in (Z.to_nat (bv_unsigned q)) in
          rewrite (wvr1_reg_atom _ _ _ _ q nq HSf) by (vm_compute; reflexivity);
          exact (ew_Ereg_nat regs _ nq q eq_refl) end
      | wvr1_pc HSf ]
  end.
Qed.

(* ================= (3) the open state with n = 0: the TAIL jump to put of ']' / '}' ================= *)
(* No UBSan guard is on this run (it leaves before the loop's guards). *)
Lemma wvc_seg_open_empty : forall (W : world tfibsegs) ms mdc E ty p STK sp0 spF FP ly S W0 mem md own lyc Sc U k
    (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssO ty) wvc_SH0 W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 -> ew E (xatom 3) = Z_to_bv 64 0 ->
  ew E 19 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     YK11.getr (ms_regs ms') 1%bv = ew E (xatom 17) ->
     YK11.getr (ms_regs ms') 2%bv = Z_to_bv 64 spF ->
     YK11.getr (ms_regs ms') 3%bv = ew E 3 ->
     YK11.getr (ms_regs ms') 4%bv = ew E 4 ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = w64 (wvc_close ty) ->
     YK11.getr (ms_regs ms') 12%bv = w64 1 ->
     (forall j r, nth_error wvc_saved j = Some r -> YK11.getr (ms_regs ms') r = ew E (xatom (5 + j))) ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_put) (ms_mem ms') (seg_rom tfibsegs) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty p STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q (HS0 & SHOK & HJ & HARU) Hty En E19 Hp
  E2 Hsp HSTK HK.
assert (HS1 : st_ok tfibsegs E
    (add_cond (add_cond (wvc_ssO ty) (mkAC BC_EQ (SOff (xatom 3) 0) (SLit 0)))
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0))) (restrict (w_H W) ms)).
{ apply st_ok_add_cond; [apply st_ok_add_cond; [exact HS0|] |].
  - rewrite branch_eq_U, U_SLit, (U_atom E (xatom 3) 0 En) by lia. vm_compute. reflexivity.
  - destruct (Z.eqb_spec p 0) as [->|Hp0]; cbv beta iota.
    + rewrite branch_eq_U, U_SLit, (U_atom E 19 0 E19) by lia. vm_compute. reflexivity.
    + rewrite branch_ne_U, U_SLit, (U_atom E 19 p E19) by lia.
      change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hp0. }
revert HS1. destruct (Z.eqb_spec p 0) as [Hp0|Hp0]; intros HS1; cbv beta iota in HS1.
all: destruct Hty as [-> | ->].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS1 HJ HARU SHOK fs_Bspan A_put.
all: lazymatch goal with
  | |- awr_ok _ _ _ (ss_mem ?ss) _ _ _ _ _ _ _ _ =>
      lazymatch ss with context [wvc_ssO ?t] => exact (wvr1_awrO E ss t STK sp0 spF FP _ _ _ _ _ eq_refl E2 Hsp HSTK) end
  | HSf : st_ok _ _ _ (restrict _ ?m), HFr : frame_of _ (ss_mem ?ss) (mrestrict _ _) (mrestrict _ _)
    |- SRr _ _ (mkCfg ?m _) _ =>
      lazymatch ss with context [wvc_ssO ?t] =>
      eapply HK;
      [ exact HJ
      | exact HARU
      | intros x Hx; exact (wvr1_frameO E ss t _ _ spF eq_refl HFr E2 x Hx)
      | wvr1_atom HSf
      | rewrite (wvr1_reg _ _ _ _ 2%bv (SOff 2 192) HSf) by (vm_compute; reflexivity);
        cbn [sv_denot]; rewrite E2; unfold WVC_F; f_equal; lia
      | wvr1_atom HSf
      | wvr1_atom HSf
      | wvr1_atom HSf
      | wvr1_lit HSf; unfold wvc_close, WVC_RBRACE, WVC_RBRACKET; cbn; lia
      | wvr1_lit HSf; lia
      | let j := fresh "j" in let r := fresh "r" in let Hj := fresh "Hj" in
        intros j r Hj;
        do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; wvr1_atom HSf |]);
        destruct j; cbn in Hj; discriminate Hj
      | wvr1_pc HSf ]
      end
  end.
Qed.

(* ================= (4) the open state with n <> 0: to the first item's indent ================= *)
(* UBSan guard 0x8418c (`bnez s10`, s10 = slt (addiw d 1) d): ruled out by the condition wvc_cSLT added before the run,
   proved (wvr1_slt) from the premises 0 <= d and d + 1 < 2 ^ 31. *)
Lemma wvc_seg_open_ind : forall (W : world tfibsegs) ms mdc E ty n d p STK sp0 spF FP ly S W0 mem md own lyc Sc U k
    (Q : world tfibsegs -> config -> Prop),
  wvc_at B E (wvc_ssO ty) wvc_SH0 W ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k ->
  ty = 5 \/ ty = 6 ->
  ew E (xatom 3) = Z_to_bv 64 n -> n <> 0 -> 0 < n < 2 ^ 54 ->
  ew E (xatom 4) = Z_to_bv 64 d -> 0 <= d -> d + 1 < 2 ^ 31 ->
  ew E 19 = Z_to_bv 64 p -> 0 <= p < alloc_ceiling ->
  bv_unsigned (ew E 2) = spF - WVC_F -> spF <= sp0 -> sp0 - STK <= spF - WVC_F ->
  (forall ms' mdc',
     ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B lyc Sc U W (ms_mem ms') mdc' ->
     (forall x : word, ~ (spF - WVC_F <= bv_unsigned x < spF) ->
        mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms')) (spF - WVC_F)) (wvc_csL p) ->
     YK11.getr (ms_regs ms') 1%bv = w64 WVC_R_IND ->
     YK11.getr (ms_regs ms') 10%bv = ew E 8 ->
     YK11.getr (ms_regs ms') 11%bv = ew E 19 ->
     YK11.getr (ms_regs ms') 12%bv = w64 (d + 1) ->
     YK11.getr (ms_regs ms') 2%bv = YK11.getr (ms_regs ms) 2%bv ->
     (forall r, In r [3; 4; 8; 9; 19]%bv -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
     YK11.getr (ms_regs ms') 18%bv = sv_denot E (SOff 9 40) ->
     YK11.getr (ms_regs ms') 20%bv = sv_denot E (wvc_shv 9 24) ->
     YK11.getr (ms_regs ms') 21%bv = w64 0 ->
     YK11.getr (ms_regs ms') 22%bv = w64 (d + 1) ->
     YK11.getr (ms_regs ms') 23%bv = w64 0 ->
     YK11.getr (ms_regs ms') 24%bv = sv_denot E (SOff 9 24) ->
     YK11.getr (ms_regs ms') 25%bv = w64 0 ->
     YK11.getr (ms_regs ms') 26%bv = w64 0 ->
     YK11.getr (ms_regs ms') 27%bv = sv_denot E (wvc_shv 9 40) ->
     ms' = mkst (ms_regs ms') (Z_to_bv 64 A_indent) (ms_mem ms') (seg_rom tfibsegs) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W ms mdc E ty n d p STK sp0 spF FP ly S W0 mem md own lyc Sc U k Q (HS0 & SHOK & HJ & HARU) Hty En Hn0 Hn
  Ex4 Hd0 Hd1 E19 Hp E2 Hsp HSTK HK.
pose proof asan_consts as (C1 & _).
assert (HS1 : st_ok tfibsegs E
    (add_cond (add_cond (add_cond (wvc_ssO ty) (mkAC BC_NE (SOff (xatom 3) 0) (SLit 0)))
      (mkAC (if p =? 0 then BC_EQ else BC_NE) (SOff 19 0) (SLit 0))) wvc_cSLT) (restrict (w_H W) ms)).
{ unfold wvc_cSLT.
  apply st_ok_add_cond; [apply st_ok_add_cond; [apply st_ok_add_cond; [exact HS0|] |] |].
  - rewrite branch_ne_U, U_SLit, (U_atom E (xatom 3) n En) by lia.
    change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. lia.
  - destruct (Z.eqb_spec p 0) as [->|Hp0]; cbv beta iota.
    + rewrite branch_eq_U, U_SLit, (U_atom E 19 0 E19) by lia. vm_compute. reflexivity.
    + rewrite branch_ne_U, U_SLit, (U_atom E 19 p E19) by lia.
      change (zcanon 0) with 0. apply negb_true_iff, Z.eqb_neq. exact Hp0.
  - rewrite branch_eq_U, U_SLit, (wvr1_slt E d Ex4 Hd0 Hd1). vm_compute. reflexivity. }
assert (Hsl : wvc_seplen p = if p =? 0 then 1 else 2) by reflexivity.
assert (Hsep : wvc_sep p = if p =? 0 then WVC_COLON else WVC_COLON_SP) by reflexivity.
revert HS1 Hsl Hsep.
destruct (Z.eqb_spec p 0) as [Hp0|Hp0]; intros HS1 Hsl Hsep; cbv beta iota in HS1, Hsl, Hsep.
all: destruct Hty as [-> | ->].
all: fsw_aj_run_to_tokU fsw_wr_tbl_ok HS1 HJ HARU SHOK fs_Bspan A_indent.
all: lazymatch goal with
  | |- awr_ok _ _ _ (ss_mem ?ss) _ _ _ _ _ _ _ _ =>
      lazymatch ss with context [wvc_ssO ?t] => exact (wvr1_awrO E ss t STK sp0 spF FP _ _ _ _ _ eq_refl E2 Hsp HSTK) end
  | HSf : st_ok _ _ _ (restrict _ ?m), HFr : frame_of _ (ss_mem ?ss) (mrestrict _ _) (mrestrict _ _)
    |- SRr _ _ (mkCfg ?m _) _ =>
      lazymatch ss with context [wvc_ssO ?t] =>
      pose proof (fsw_region_nth _ _ _ 0 _ HSf eq_refl) as HR0;
      destruct HR0 as (_ & _ & _ & HCs);
      cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HCs; rewrite E2 in HCs;
      eapply HK;
      [ exact HJ
      | exact HARU
      | intros x Hx; exact (wvr1_frameO E ss t _ _ spF eq_refl HFr E2 x Hx)
      | unfold wvc_csL; rewrite Hsl, Hsep;
        lazymatch goal with |- Forall ?P ?l0 => let l1 := eval vm_compute in l0 in change (Forall P l1) end;
        repeat (apply Forall_cons; [wvr1_ckL HCs E19 Hsl |]); apply Forall_nil
      | wvr1_lit HSf; unfold WVC_R_IND; lia
      | wvr1_atom HSf
      | wvr1_atom HSf
      | rewrite (wvr1_reg _ _ _ _ 12%bv (SAlu ALU_ADD (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SLit 0)) HSf)
          by (vm_compute; reflexivity);
        exact (proj2 (wvr1_d1 E d Ex4 Hd0 Hd1))
      | apply (wvr1_reg_same _ _ _ _ _ _ _ HSf HS0); vm_compute; reflexivity
      | let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
        apply (wvr1_reg_same _ _ _ _ _ _ _ HSf HS0); vm_compute; reflexivity
      | wvr1_sv HSf
      | wvr1_sv HSf
      | wvr1_lit HSf; lia
      | rewrite (wvr1_reg _ _ _ _ 22%bv (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) HSf) by (vm_compute; reflexivity);
        exact (proj1 (wvr1_d1 E d Ex4 Hd0 Hd1))
      | wvr1_lit HSf; lia
      | wvr1_sv HSf
      | wvr1_lit HSf; lia
      | rewrite (wvr1_reg _ _ _ _ 26%bv
          (SAlu ALU_SLT (SAluw ALU_ADD (SOff (xatom 4) 0) (SLit 1)) (SOff (xatom 4) 0)) HSf)
          by (vm_compute; reflexivity);
        exact (wvr1_slt_den E d Ex4 Hd0 Hd1)
      | wvr1_sv HSf
      | wvr1_pc HSf ]
      end
  end.
Qed.
End W.
