(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v, with its module paths and module names changed; 202 of its 245 lines of code are new or changed and 315 lines of the source are left out. *)
(* Image B: check_text_seg7 at 0x84148 is image A's code (lib/A/Prog/check_text_seg7_A.v) with each address 0x664
   higher, the callees at image B's addresses (diginet_seg7 0x86978, CPgEncU.v cdcU_seg7_specX; owed_seg7 0x84a54,
   CPgChkU.v cdcU_owed_seg7_specX), the image constants CB_ (lib/AU/Prog/CPgWalkU.v) and three differences:
   - image B computes s0 = c + 1 (0x84180) before the flag (0x84184-0x84190) instead of after, inside the run from
     owed_seg7's return to the bne at 0x84194, so the walk's steps are unchanged;
   - diginet_seg7's image-B contract asks for cimg_rd of its table [(CB_SEG7, 364)] (image A's asked for the read-only
     data, the table's in_roP and its crd_ok), which the walk gives from the caller's cimg_rd (its first row, HCI1)
     at the callee's window by cts_cimg, as for owed_seg7;
   - one unimp follows the abort call.
   .data.rel.ro .. .got is [0x9dba0, 0x9f128) at image B. Image A's notes follow, with image B's addresses. *)
(* check_text_seg7 (fuzz_codec.c:454-466) at image B: 0x84148, 30 instructions, frame 48, no instrumented check;
   against lib/AU/Prog/CPgChkU.v's cdcU_check_seg7_specX, from the contracts of its two callees diginet_seg7
   (CPgEncU.v cdcU_seg7_specX at 0x86978) and owed_seg7 (CPgChkC.v cdcU_owed_seg7_specX at 0x84a54).
   0x84148-0x84168 open the frame, save ra and s0-s3 (the walk's only stores), s0 = c = 0, s2 = 1, s3 = 256. The loop
   head 0x8416c is brought to one state at both arrivals (cts_norm: only the save area, only the atom facts of sp and
   SB, s0 = atom 200 = c, the dead registers in atoms 201.., s2 = 1, s3 = 256), and the loop is the induction LOOP
   over the count 256 - c. One turn: `zext.b a0,s0; jal diginet_seg7` and `mv s1,a0; mv a0,s0; jal owed_seg7`, each
   through its contract by CPgWalkCall.v's cpw_call_reseat (the callees' windows lie below the save area; their
   cimg_rd / crd_ok from the caller's cimg_rd at the callee's sp, cts_cimg / cw_crd_img, the read-only data kept by
   the walk's tcj_kept, cts_aro); then s2 = ((r1 xor r2) != 0) - 1 and s2 stays 1 (cts_U_flag: r1 = seg7(c) =
   owed_seg7(c), the agreement premise), s0 = c + 1 (cts_U_inc). 0x84194 bne s0,s3: taken back to the loop head with
   c + 1 (s2 pinned to 1); not taken (c = 255) to 0x84198 beqz s2, whose taken side (the abort call) is refuted, then
   the epilogue and `ret` (cpw_leaf, the memory clause the walk's tcj_kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CodecRo CodecGlobs CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkKeptU CPgWalkCallU CPgWalkStrU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers the loop head holds in fresh atoms: s0 (= c) first, then the dead ones *)
Definition cts_RL : list (bv 5) := [8; 1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
(* The loop head's state at 0x8416c, the same at the first arrival and at the back edge: only the save area, only
   the atom facts of sp and SB, s0 and the dead registers in the atoms 200.. (s0 = atom 200), s2 = 1, s3 = 256.
   First s0 goes to atom 300 (its old expression may use the window 200..), then the window 200.. takes the values
   of cts_RL. The new environment is named Ev with its equation HEv. *)
Ltac cts_norm Ev HEv :=
cw_drop_gb;
lazymatch goal with HS : st_ok _ ?E0 ?ssx ?msx |- _ =>
  let fa := eval vm_compute in cw_atoms in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_facts_incl3 tfibsegs E0 ssx msx fa [] [] HS ltac:(incl_lit_tac) ltac:(intros ? [])
    ltac:(intros ? [])) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end;
lazymatch goal with HS : st_ok _ ?E0 ?ssx (restrict ?Hh ?msx) |- _ =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_havoc_win tfibsegs 300 E0 ssx (restrict Hh msx) [getr (ms_regs msx) (8%bv : bv 5)] HS
    ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  set_regs_rec HS 300%nat [getr (ms_regs msx) (8%bv : bv 5)] 0%nat [(8%bv : bv 5)] end;
lazymatch goal with HS : st_ok _ ?E0 ?ssx (restrict ?Hh ?msx) |- _ =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_havoc_win tfibsegs 200 E0 ssx (restrict Hh msx) (map (getr (ms_regs msx)) cts_RL) HS
    ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS;
  let vals := eval cbn [map cts_RL] in (map (getr (ms_regs msx)) cts_RL) in
  change (map (getr (ms_regs msx)) cts_RL) with vals in HS;
  let rl := eval cbv [cts_RL] in cts_RL in
  set_regs_rec HS 200%nat vals 0%nat rl end;
lazymatch goal with HS : st_ok _ ?Enew _ _ |- _ => remember Enew as Ev eqn:HEv in HS end.

Lemma cts_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.
(* `addiw s0, s0, 1` on c < 256 *)
Lemma cts_U_inc : forall E c, ew E 200 = Z_to_bv 64 c -> 0 <= c < 256 ->
U E (SAluw ALU_ADD (SOff 200 0) (SLit 1)) = c + 1.
Proof.
intros E c H Hc. rewrite U_of_S, S_SAluw, (U_atom E 200 c H) by lia. rewrite U_lit by lia. cbn [zalu_raw].
rewrite (Z.mod_small c) by lia. change (1 mod 2 ^ 32) with 1.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (4294967296 / 2) with 2147483648.
rewrite (Z.mod_small (c + 1 + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the flag of 0x84180-0x84190, s2 = ((r1 xor r2) != 0) - 1 and 1, with s2 = 1 before: 1 when r1 = r2 *)
Lemma cts_U_flag : forall E a b v, ew E a = v -> ew E b = v ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff a 0) (SOff b 0))) (SLit (-1))) (SLit 1)) = 1.
Proof.
intros E a b v Ha Hb. rewrite !U_SAlu, !U_SLit, !U_SOff, Ha, Hb. cbn [zalu_raw].
rewrite Z.lxor_nilpotent. vm_compute. reflexivity.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cts_relro_img : forall a, 0x9dba0 <= a < 0x9f128 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Variable B : asyms.
(* the read-only data stays the image's across a stretch the walk keeps (tcj_kept clause 3) *)
Lemma cts_aro : forall T lyc Sc (W : world tfibsegs) memc Wc mc sp (E : Z -> Prop),
arodata_okP tfibsegs CB_RLO CB_RHI B (aview tfibsegs (w_H W) memc) ->
tcj_kept tfibsegs B T lyc Sc W memc Wc mc sp E ->
arodata_okP tfibsegs CB_RLO CB_RHI B (aview tfibsegs (w_H Wc) mc).
Proof.
intros T lyc Sc W memc Wc mc sp E HRO (_ & _ & K3 & _) a Hro Ho He.
rewrite (K3 a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (cts_relro_img a Hr)].
Qed.
(* a contract's cimg_rd at a deeper window, over memory the walk kept *)
Lemma cts_cimg : forall T lyc Sc (W : world tfibsegs) memc Wc mc sp (E : Z -> Prop) sp1 T1 sp2 T2 l,
cimg_rd tfibsegs B CB_RLO CB_RHI W memc sp1 T1 l ->
tcj_kept tfibsegs B T lyc Sc W memc Wc mc sp E ->
sp2 <= sp1 -> sp1 - T1 <= sp2 - T2 ->
cimg_rd tfibsegs B CB_RLO CB_RHI Wc mc sp2 T2 l.
Proof.
intros T lyc Sc W memc Wc mc sp E sp1 T1 sp2 T2 l (HRO & HF) KT H1 H2. split; [exact (cts_aro _ _ _ _ _ _ _ _ _ HRO KT)|].
eapply Forall_impl; [|exact HF]. intros r (Hro & Hq & Hn & Hqn & Ham & Hcw & Himg & HU).
split; [exact Hro|]. split; [exact Hq|]. split; [exact Hn|]. split; [exact Hqn|]. split; [exact Ham|].
split; [unfold coff_win in *; lia|]. split; [exact Himg | exact HU].
Qed.
End a.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SEG7 : cdcU_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 0x86978.
Hypothesis OWED : cdcU_owed_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_GLYPH CB_ROSTRS 0x84a54.
Theorem check_text_seg7_B_holds :
cdcU_check_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS 0x84148.
Proof.
unfold cdcU_check_seg7_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HEN HCI HAG.
pose proof HEN as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_seg7 HEN
  ltac:(unfold TB_check_seg7, TB_owed_seg7; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof (cw_entry_base B TL LAWS 0x84148 48 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  TB_check_seg7 HEN ltac:(unfold TB_check_seg7, TB_owed_seg7; lia) ltac:(vm_compute; reflexivity)) as HS.
unfold TB_check_seg7, TB_owed_seg7 in Hwlo, Hceil, H46, Hpres.
remember (Ereg regs (cw_extra [])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (cw_ew_reg regs _ 1 1%bv eq_refl)).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (cw_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
clear HE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) TB_check_seg7 cno_wr HJ0
  ltac:(unfold TB_check_seg7, TB_owed_seg7; lia) ltac:(lia)) as KT.
unfold TB_check_seg7, TB_owed_seg7 in KT.
assert (HFRS : frames Sc = frames Sc) by reflexivity.
assert (HPERM : Permutation (ablocks B lyc Sc) (ablocks B lyc Sc)) by apply Permutation_refl.
assert (HIO : same_io mdc mdc) by apply same_io_refl.
assert (HMO : mo_le MT Sc Sc 0) by (apply mo_le_refl; exact MTL).
pose proof HJ0 as HJ.
destruct HCI as (HRO & HROWS).
(* diginet_seg7's table row, the first row of the caller's cimg_rd *)
assert (HCI1 : cimg_rd tfibsegs B CB_RLO CB_RHI W memc (spZ regs) TB_check_seg7 [(CB_SEG7, 364)])
  by (split; [exact HRO | apply Forall_cons; [exact (Forall_inv HROWS) | apply Forall_nil]]).
assert (HCI2 : cimg_rd tfibsegs B CB_RLO CB_RHI W memc (spZ regs) TB_check_seg7 ((CB_GLYPH, 464) :: CB_ROSTRS))
  by (split; [exact HRO | exact (Forall_inv_tail HROWS)]).
clear HROWS.
unfold cfg_at. change (w64 0x84148) with (Z_to_bv 64 0x84148).
(* 0x84148-0x84168: the frame, the saves of ra and s0-s3, s0 = 0, s2 = 1, s3 = 256 *)
cw_run_to cw_awr_stk 0x8416c.
cpw_keep cw_kwr_stk.
(* the loop head, first arrival (c = 0) *)
rreg HS (8%bv : bv 5) R8.
cts_norm Ec HEc.
assert (HAEc : env_agree 32 (Ereg regs (cw_extra [])) Ec)
  by (rewrite HEc; apply env_agree_havoc_ge; [lia|]; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (B2c : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite HEc, !ew_havoc_old by lia; exact B2).
assert (E200 : ew Ec 200 = Z_to_bv 64 0)
  by (rewrite HEc, (ew_havoc_new _ 200 _ 0 (Z_to_bv 64 0)) by (cbn; lia); exact R8).
clear HEc HAE B2 R8 SHOK.
lazymatch goal with HS : st_ok _ _ ?ssL (restrict (w_H W) ?ms1) |- SRr _ _ _ ?Q =>
assert (SHOK : sh_ok tfibsegs CW_Bx [] Ec (mrestrict (w_H W) (ms_mem ms1))) by constructor;
assert (LOOP : forall (n : nat) (c : Z) (Wc : world tfibsegs) (Ec : env) (ms : machine_state) (mdd : Model) lyd Sd,
  Z.of_nat n = 256 - c -> 0 <= c < 256 ->
  st_ok tfibsegs Ec ssL (restrict (w_H Wc) ms) ->
  env_agree 32 (Ereg regs (cw_extra [])) Ec -> bv_unsigned (ew Ec 2) = spZ regs -> ew Ec 200 = Z_to_bv 64 c ->
  sh_ok tfibsegs CW_Bx [] Ec (mrestrict (w_H Wc) (ms_mem ms)) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyd Sd Wc (ms_mem ms) mdd k ->
  tcj_kept tfibsegs B (48 + 16) lyc Sc W memc Wc (ms_mem ms) (spZ regs) cno_wr ->
  frames Sd = frames Sc -> Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) -> same_io mdc mdd ->
  mo_le MT Sc Sd 0 ->
  SRr tfibsegs Wc (mkCfg ms mdd) Q) end.
2: { eapply (LOOP 256%nat 0); [lia | lia | exact HS | exact HAEc | exact B2c | exact E200 | exact SHOK | exact HJ
     | exact KT | exact HFRS | exact HPERM | cpw_io | exact HMO]. }
clear HS HAEc B2c E200 SHOK HJ KT HFRS HPERM HIO HMO.
induction n as [|n IH]; intros c Wc Ecur msc mdd lyd Sd Hn Hc HS HAE B2 E200 SHOK HJ KT HFRS HPERM HIO HMO.
{ cbn in Hn. lia. }
(* 0x8416c zext.b a0,s0; jal diginet_seg7 *)
cw_run_to cw_awr_stk 0x86978.
cpw_keep cw_kwr_stk.
cpw_call_reseat (fun STK' sp0' FP' ly' S' W0' mem0' md0' own' lyc' Sc' W' memc' mdc' k' regs' =>
    SEG7 STK' sp0' FP' ly' S' W0' mem0' md0' own' lyc' Sc' W' memc' mdc' k' regs' c) 48
  ltac:(idtac; first
    [ lazymatch goal with |- getr (ms_regs _) 10 = w64 _ =>
        let R := fresh "R" in cw_r10 R; rewrite R, denot_lit_U; unfold w64; f_equal;
        rewrite U_and_lit, (U_atom _ 200 c E200) by lia; apply cts_land255; lia end
    | lazymatch goal with Esp : spZ (ms_regs _) = _ |- cimg_rd _ _ _ _ _ _ _ _ _ =>
        rewrite Esp; apply (cts_cimg B _ _ _ _ _ _ _ _ _ (spZ regs) TB_check_seg7 _ _ _ HCI1 KT);
        [lia | unfold TB_check_seg7, TB_owed_seg7, TB_seg7; lia] end
    | lia ])
  [0]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
rewrite HRc in HA0c. clear HRc. rename HA0c into EV1.
(* 0x84174 mv s1,a0; mv a0,s0; jal owed_seg7 *)
cw_run_to cw_awr_stk 0x84a54.
cpw_keep cw_kwr_stk.
cpw_call_reseat (fun STK' sp0' FP' ly' S' W0' mem0' md0' own' lyc' Sc' W' memc' mdc' k' regs' =>
    OWED STK' sp0' FP' ly' S' W0' mem0' md0' own' lyc' Sc' W' memc' mdc' k' regs' c) 48
  ltac:(idtac; first
    [ lazymatch goal with |- getr (ms_regs _) 10 = w64 _ =>
        let R := fresh "R" in cw_r10 R; rewrite R, sv_denot_SOff0, E200; reflexivity end
    | lazymatch goal with Esp : spZ (ms_regs _) = _ |- cimg_rd _ _ _ _ _ _ _ _ _ =>
        rewrite Esp; apply (cts_cimg B _ _ _ _ _ _ _ _ _ (spZ regs) TB_check_seg7 _ _ _ HCI2 KT);
        [lia | unfold TB_check_seg7, TB_owed_seg7; lia] end
    | lia ])
  [0]%nat ltac:(fun K J1 J2 => cpw_kept_std K J1 J2) ltac:(intros ? []).
rewrite HRc in HA0c. clear HRc. rename HA0c into EV2.
(* 0x84180 addiw s0 / xor / snez / addiw / and s2; stop at 0x84194 bne s0,s3 *)
cw_run cw_awr_stk.
cpw_keep cw_kwr_stk.
rewrite (Z.mod_small c 256 Hc), (HAG c Hc) in EV1.
lazymatch type of EV1 with ew ?Ex _ = _ =>
  pose proof (cts_U_flag Ex 222 238 _ EV1 EV2) as UF;
  assert (E200' : ew Ex 200 = Z_to_bv 64 c) by exact E200;
  pose proof (cts_U_inc Ex c E200' Hc) as UI end.
(* 0x84194 bne s0,s3: s0 = c + 1 *)
cw_branch Hb.
- (* taken, c + 1 <> 256: the back edge to 0x8416c *)
  rewrite branch_ne_U, UI, U_lit in Hb by lia.
  assert (Hc1 : c + 1 <> 256) by (intros C; rewrite C in Hb; discriminate Hb).
  cw_run_to cw_awr_stk 0x8416c.
  cpw_keep cw_kwr_stk.
  (* s2 = 1 *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
    let Hv := fresh "Hv" in
    assert (Hv : sv_denot Ev (SLit 1) = getr (ms_regs (restrict Hh msx)) (18%bv : bv 5))
      by (rewrite (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (18%bv : bv 5) HS);
          let e := eval vm_compute in (sr_get (ss_regs ssx) (18%bv : bv 5)) in
          change (sv_denot Ev (SLit 1) = sv_denot Ev e); rewrite (denot_lit_U Ev e), UF; reflexivity);
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx (restrict Hh msx) (18%bv : bv 5) (SLit 1) HS
      ltac:(vm_compute; reflexivity) Hv) as HS3;
    clear HS Hv; rename HS3 into HS; norm_ss HS end.
  (* s0 = c + 1 *)
  lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) |- _ =>
    assert (R8 : getr (ms_regs msx) (8%bv : bv 5) = Z_to_bv 64 (c + 1))
      by (refine (eq_trans (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (8%bv : bv 5) HS) _);
          let e := eval vm_compute in (sr_get (ss_regs ssx) (8%bv : bv 5)) in
          change (sv_denot Ev e = Z_to_bv 64 (c + 1)); rewrite (denot_lit_U Ev e), UI; reflexivity) end.
  lazymatch goal with HAE : env_agree 32 _ ?Ev, B2 : bv_unsigned (ew ?Ev 2) = _ |- _ =>
    cts_norm Ecn HEcn;
    assert (HAEc : env_agree 32 (Ereg regs (cw_extra [])) Ecn)
      by (rewrite HEcn; apply env_agree_havoc_ge; [lia|]; apply env_agree_havoc_ge; [lia | exact HAE]);
    assert (B2c : bv_unsigned (ew Ecn 2) = spZ regs) by (rewrite HEcn, !ew_havoc_old by lia; exact B2) end.
  assert (E200c : ew Ecn 200 = Z_to_bv 64 (c + 1))
    by (rewrite HEcn, (ew_havoc_new _ 200 _ 0 (Z_to_bv 64 0)) by (cbn; lia); exact R8).
  lazymatch goal with HS : st_ok _ Ecn _ (restrict (w_H ?Wx) ?msx) |- _ =>
    assert (SHOKc : sh_ok tfibsegs CW_Bx [] Ecn (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
  eapply (IH (c + 1)); [lia | lia | exact HS | exact HAEc | exact B2c | exact E200c | exact SHOKc | exact HJ
    | exact KT | exact HFRS | exact HPERM | cpw_io | exact HMO].
- (* not taken, c + 1 = 256: 0x84198 beqz s2 *)
  rewrite branch_ne_U, UI, U_lit in Hb by lia.
  cw_run cw_awr_stk.
  cpw_keep cw_kwr_stk.
  cw_branch Hb2.
  { exfalso. rewrite branch_eq_U, UF, U_lit in Hb2 by lia. discriminate Hb2. }
  cw_run cw_awr_stk.
  cpw_keep cw_kwr_stk.
  lazymatch goal with HAE : env_agree 32 _ ?Ev |- _ =>
    assert (E1c : ew Ev 1 = getr regs 1) by (rewrite (proj1 HAE 1%nat ltac:(lia)); exact (cw_ew_reg regs _ 1 1%bv eq_refl)) end.
  cpw_leaf ltac:(idtac; exact KT) ltac:(cbv beta; exact I).
Qed.
End d.
End b.
