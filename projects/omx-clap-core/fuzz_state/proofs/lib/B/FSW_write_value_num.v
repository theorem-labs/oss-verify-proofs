(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths, addresses and numbers changed; 11 of its 318 lines of code are new or changed and 1385 lines of the source are left out. *)
(* write_value's NUMBER arm (fs.asan-ubsan 0x84010, preset_file.c:525-575, case PJ_NUMBER), image B, against
   lib/B/FSH_Fn_writer.v's write_value_spec_at (statement set a working branch 50968be8342, no CTX).
   rule 24 (02:59Z form): proves no function (kind: segment lemma) - the number arm of write_value B.
   Template for the S0 statement shape: image A's wv_num (a working branch 9e8a0cdbf33,
   lib/A/FSW_write_value.v:1512-1812, on the same CTX-drop statement set), with the helpers only it uses
   (wv_aview_unpoison_eq, wv_apresent_unpoison, wv_rt_post_conv, wv_chunk_move, wv_saved / wv_xsR / wv_cs0, wv_frameR,
   wv_garr8_prefix), same names. Template for image B's code: a working branch 4309d52a177
   lib/B/Prog/write_value_leaf.v (bespoke statements, template only; no bridge).
   B's code, MEASURED on the pinned fuzz_state.asan-ubsan (sha256 5ac5ce09..., fuzz_state.objdump.txt):
     0x84010 addi sp,sp,-192 (frame 192 = FRAME_write_value); ra / s0 .. s11 saved at 184, 176, 168, 160 .. 88;
     d (a3) at 24; v & 7 at 16; the shadow base at 72; the node's shadow address at 80.
     0x8404c beqz a1,0x84444  UBSan guard 1 (nonnull: the root node v).
     0x84060 bnez a0,0x84444  UBSan guard 2 (alignment: a0 = v & 7).
     0x84084 lb (shadow of v) / 0x84088 bnez -> 0x84448 (ASan slow path); 0x8408c lw ty; 0x84094 bltu 6,ty;
     jump table at .rodata 0x21000 (seven 4-byte offsets, re-read from B's image: 0x633d8 0x633e8 0x6338c 0x63398
     0x632e8 0x630b4 0x630b4); ty = 3 (number) -> 0x84398.
     0x84398 addi a0,s1,16; ASan check of the 8-byte load (lbu shadow(v + 16), bnez -> 0x84498 report);
     0x843b0 ld s1,16(v) (str); 0x843b4 bnez s1 (str = NULL would take the literal .str.10 "0" at 0x21140);
     0x843c4 jal 0x426c4 (PC_strlen, __interceptor_trampoline_strlen), returning to 0x843c8;
     0x843c8 mv a2,a0; mv a0,s0; mv a1,s1; j 0x84408: the epilogue reloads ra, s0 .. s11 and TAIL-jumps to put 0x8449c.
   (image A: frame 176, strlen call at 0x83f54 returning to 0x83f58, tail put 0x8418c.)
   UBSan guards (the image is TRAP mode: one unimp at 0x84444, eleven branches to it). Of the eleven, exactly TWO lie on
   this arm's path, both in the shared entry block before the type dispatch; the other nine (0x8418c, 0x841d8,
   0x841e0, 0x841e4, 0x841e8, 0x841f4, 0x8424c, 0x84250, 0x84268) are in the array / object loop only:
     0x8404c `beqz a1`: a1 = v. Untaken because 4096 <= v: FSH_Fn_reader.pobj (the root node is a live fake frame or a
              live heap block; wv_pobj's 4096 <= v), carried into the run as the atom fact (11, mkAF 4096 (WV_CEIL - 56) 3)
              of wv_gf, which wv_start establishes from the premise `FSH_Fn_reader.pobj tfibsegs B ly S W mem v`.
     0x84060 `bnez a0`: a0 = v & 7. Untaken because v mod 8 = 0: FSH_Fn_reader.pobj again (its `v mod 8 = 0`), the
              alignment field 3 of the same atom fact (2 ^ 3 | v).
   The symbolic run below (fsw_aj_run_to_tokU from wv_start's state to PC_strlen) decides both branches from that
   fact; it takes no premise beyond write_value_spec_at's own.
   CHECKLIST of record (a Theorem Labs lane's reloc-check/report-sites-B.tsv rows 116-126, write_value B): the rows this arm's
   path reaches, and how each is refuted (the rest are the array / object loop's and the string arm's: 116 0x842ac,
   119 0x8446c, 120 0x84474, 121 0x8447c, 122 0x84484, 123 0x84488, 124 0x84490, 125 0x84494):
     row 117  unimp 0x84444: of its eleven edges, 0x8404c and 0x84060 only (above).
     row 118  __asan_report_load4 0x84458, entered by 0x84088 bnez -> 0x84448 (the 4-byte load of v->type): the
              shadow byte of v is 0, since wv_SH's entry (mkSHE 11 0 56) says [v, v + 56) is addressable
              (FSH_Fn_reader.pobj's range_addressable ... v 56, via wv_start's sh_ok) and v is 8-aligned.
     row 126  __asan_report_load8 0x84498, entered by 0x843ac bnez -> 0x84498 (the 8-byte load of v->str at v + 16):
              the shadow byte of v + 16 is 0 by the same entry ([v + 16, v + 24) inside [v, v + 56), 8-aligned).
   The token run decides both checks from wv_SH; neither branch is taken.
   Section hypotheses: FsShadowSyms (HSS), fs_img_facts (IMG), the tail callee put_spec (HPUT, through
   FSW_write_value_entry.wv_tail_put) and the strlen interceptor astrlen_realizesU at B's PC_strlen (HSLEN), as A's
   walk. The entry part (wv_start, wv_awr0, wv_frame0, wv_tail_put, wv_spec_on, ...) is a Theorem Labs lane's
   lib/B/FSW_write_value_entry.v (c00814d3d74), imported. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_pj FSH_Fn_writer FSW_write_value_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= the number arm: strlen of the text, then a tail call of put ================= *)
(* the shadow-base cells (lib/B/FSH_Base.FsShadowSyms) and the image facts (lib/B/FSH_Rt.fs_img_facts), as A's walk *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the tail callee put (FSW_write_value_entry.wv_tail_put takes it) *)
Hypothesis HPUT : put_spec B tfibsegs.
(* the strlen interceptor's contract (S0's FSH_Gen.astrlen_realizesU at fs.asan-ubsan's PC_strlen 0x426c4;
   lib/B/FSH_Rt.FsRt.fr_strlen) *)
Hypothesis HSLEN : astrlen_realizesU tfibsegs B PC_strlen.

(* aview / presence through unpoison follow the raw memory's *)
Lemma wv_aview_unpoison_eq : forall (H : word -> bool) U (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> aview tfibsegs H (unpoison U m') a = aview tfibsegs H (unpoison U m) a.
Proof.
intros H U m m' a E. unfold aview, mbyte, mrestrict, unpoison in *.
destruct (H (Z_to_bv 64 a)); [reflexivity|].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity | exact E].
Qed.
Lemma wv_apresent_unpoison : forall (H : word -> bool) U (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (unpoison U m) a -> apresent H (unpoison U m') a.
Proof.
intros H U m m' Hp a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in *.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [exists (Z_to_bv 8 0); reflexivity|].
destruct (Hp a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
Qed.
(* a runtime callee's ARU-form post (FSH_Gen.rt_post_roU) in the shape FSW_K.fsw_intrin_atU takes *)
Lemma wv_rt_post_conv : forall K ly S U (W : world tfibsegs) regs mem md (R : Z -> Prop) W' c',
  upoison_ok B ly S U ->
  rt_post_roU tfibsegs B K ly S U W regs mem md R W' c' ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
    ARU tfibsegs B ly S U W mem' md' /\ same_but_materialized md md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
       aview tfibsegs (w_H W) (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) /\
    (forall a, apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) (unpoison U mem') a) /\
    (aregs_preserved regs regs' /\ (exists v, getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a)).
Proof.
intros K ly S U W regs mem md R W' c' OK (-> & regs' & mem' & md' & v & Ec & HAR & PO & HP & Hs & G10 & Hv & HR & Hfr & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [exact Ec|]. split; [split; [exact HAR | split; [exact OK | exact PO]]|]. split; [exact Hs|].
split; [intros a Ha Hn; apply wv_aview_unpoison_eq; exact (Hfr a Ha Hn)|].
split; [exact (wv_apresent_unpoison (w_H W) U mem mem' Hpr)|].
split; [exact HP|]. split; [exists v; auto | exact Hfr].
Qed.
(* a chunk read at one base / env, re-read at another base / env holding the same value *)
Lemma wv_chunk_move : forall E E2 m base base2 off off2 e e2,
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 e)) -> base + off = base2 + off2 ->
  sv_denot E2 e2 = sv_denot E e -> YP09.chunk_ok tfibsegs E2 m base2 (YP09.mkChunk off2 (CVal 8 e2)).
Proof.
intros E E2 m base base2 off off2 e e2 H Hb He i Hi. destruct (H i Hi) as (b & Hc & Hm). exists b.
cbn [YP09.c_off YP09.c_val YP09.cbyte] in *. rewrite He. split; [exact Hc|].
replace (base2 + off2 + i) with (base + off + i) by lia. exact Hm.
Qed.

(* the frame slots B's prologue wrote, as the epilogue reloads them after the strlen call: 72 the shadow base, 88 .. 184
   the thirteen saved entry registers (s11 .. s2, s1, s0, ra; MEASURED 0x84014 .. 0x84044), each an extra atom
   xatom (5 + k) of the resumed env (A: 64 and 72 .. 168 in a frame of 176) *)
Definition wv_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition wv_xsR (regs : bvmap 5 word) (str kids keys n d : Z) : list word :=
  wv_xs str kids keys n ++ [Z_to_bv 64 d] ++ map (fun r => YK11.getr regs r) wv_saved.
Definition wv_cs0 : list YP09.chunk :=
  YP09.mkChunk 72 (CVal 8 (SOff 32 0))
  :: map (fun k => YP09.mkChunk (88 + 8 * Z.of_nat k) (CVal 8 (SOff (xatom (5 + k)) 0))) (seq 0 13).
(* a run from a resumed state with no extra region writes only the frame [sp - 192, sp) *)
Lemma wv_frameR : forall E r cs (m m' : word -> option byte) sp,
  frame_of E (ss_mem (fss_retT r 192 cs [] [])) m m' -> bv_unsigned (ew E 2) = sp - 192 ->
  forall x : word, ~ (sp - 192 <= bv_unsigned x < sp) -> m' x = m x.
Proof.
intros E r cs m m' sp HF E2 x Hx. apply HF. intros (rg & Hin & Hr).
cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]];
  cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  try (rewrite E2 in Hr); lia.
Qed.
Lemma wv_garr8_prefix : forall m p (l l' : list Z), garr8 tfibsegs m p (l ++ l') -> garr8 tfibsegs m p l.
Proof.
intros m p l l' H j Hj. destruct (H j ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hj. split; assumption.
Qed.

(* the arm. The first run, from wv_start's entry state to the strlen call, passes the UBSan guards 0x8404c (v <> 0)
   and 0x84060 (v & 7 = 0) on wv_gf's atom fact for v (from FSH_Fn_reader.pobj), the two inline ASan checks (the
   node's shadow bytes, wv_SH), the type check and the jump table (wv_jt, entry 3), and the str = NULL branch on
   str's atom fact [4096 + HEAD, WV_CEIL] (a live reader block, wv_rblock_low). *)
Lemma wv_num : forall k, wv_spec_on B (fun t => exists txt bits, t = PjTree.JNum txt bits) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (txt & bits & ->) Hdep
  HPRE HHEADS HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot
  Hplain Hfoot HROOM HCAP HCL HBUD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HUOK & HUPO).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (wv_stk_frame (2 - k)) as HSF.
assert (HSTR : WV_F + STK_RT_STR <= STK_write_value (2 - k))
  by (destruct (2 - k)%nat; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value, WV_F; cbn [fold_right]; lia).
assert (HRS : STK_RT_STR = 8192) by reflexivity.
assert (HWF : WV_F = 192) by reflexivity.
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & (_ & _ & _ & _ & _ & kk & HCS & ED)).
assert (HinD : In (str, kk) D) by (rewrite ED; left; reflexivity).
destruct (HD str kk HinD) as [HinUL Hne].
pose proof (HUL str kk HinUL) as HRB. pose proof HRB as (_ & _ & Hkk & _).
pose proof (wv_rblock_low B ly S W _ md mem str kk HAR HRB) as (Hs1 & Hs2).
destruct (wv_start B HSS IMG k ly S U W regs mem md ch ot v _ num str kids keys n cap0 (4096 + HEAD) WV_CEIL buf cap HPRE G11 HPO HH
  ltac:(unfold WV_CEIL; lia) ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
set (E := Ereg regs (fs_extraT ++ wv_xs str kids keys n)) in *.
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan PC_strlen.
- apply (wv_awr0 B); [exact E2 | lia | exact HSF].
- (* ---- at the strlen call (0x843c4 jal 0x426c4) ---- *)
  lazymatch goal with HS : st_ok _ _ ?ssf _ |- _ => set (ssT := ssf) in HS end.
  set (mdT := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (M16 : forall a b c, a mod 16 = 0 -> b mod 16 = 0 -> c mod 16 = 0 -> (a - b - c) mod 16 = 0)
    by (intros a0 b0 c0 Ha Hb Hc; rewrite Zminus_mod, (Zminus_mod a0 b0), Ha, Hb, Hc; reflexivity).
  assert (R1T : getr (ms_regs ms) 1%bv = Z_to_bv 64 0x843c8)
    by exact (fsw_reg_lit (w_H W) E ssT ms 1%bv 0x843c8 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
  assert (SPT : spZ (ms_regs ms) = spZ regs - 192)
    by (unfold spZ; exact (fsw_reg_off (w_H W) E ssT ms 2%bv 2 (-192) (spZ regs) HS ltac:(vm_compute; reflexivity) E2
          ltac:(lia))).
  assert (R3T : getr (ms_regs ms) 3%bv = getr regs 3%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 3%bv 3%bv 3%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R4T : getr (ms_regs ms) 4%bv = getr regs 4%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 4%bv 4%bv 4%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R10T : getr (ms_regs ms) 10%bv = w64 str)
    by (rewrite (fsw_reg_extra (w_H W) regs _ ssT ms 10%bv 1 HS ltac:(vm_compute; reflexivity)); reflexivity).
  pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREU) as HARUe.
  assert (SB1 : rsame W mem (ms_mem ms)).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (wv_frame0 E _ _ _ mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
    rewrite (wz x ltac:(lia)). unfold WV_F in *. lia. }
  assert (HROMT : rom_view tfibsegs W (ms_mem ms)).
  { intros a Ha. pose proof Ha as (sg & Hin & Hw & Hr).
    assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | lia]).
    pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
    rewrite (rsame_aview W mem (ms_mem ms) a SB1 ltac:(lia)).
    exact (wv_rom_view B _ ly S U W regs mem md ch IMG HPREU HRO a Ha). }
  assert (HCSOKT : cstr_ok tfibsegs W (ms_mem ms) str txt)
    by exact (rsame_cstr_ok W mem (ms_mem ms) str txt SB1 (wv_cstr_ok_node B ly S U W mem md UL str kk txt HARUe HHEADS
      HUL HCS)).
  assert (HPRET : ecall_preU_k tfibsegs B STK_RT_STR ly S U W (ms_regs ms) (ms_mem ms) mdT).
  { apply (fsw_ecall_preU_k_at B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W (ms_mem ms) mdT 0 (ms_regs ms) (spZ regs - 192 - ot) STK_RT_STR HJ HARU0).
    - rewrite SPT. lia.
    - exact (M16 (spZ regs) 192 ot Hsp16 eq_refl Hot16).
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite R1T. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite R3T. exact Hgp.
    - rewrite R4T. exact Htp. }
  pose proof HSS as [HBgot HBcell].
  pose proof (wv_cstr_ok_node B ly S U W mem md UL str kk txt HARUe HHEADS HUL HCS) as HCSOK0.
  (* the call state's registers the resume and the jump read: s0 = the entry a0 (o), s1 = str *)
  assert (R8T : getr (ms_regs ms) 8%bv = getr regs 10%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 8%bv 10%bv 10%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R9T : getr (ms_regs ms) 9%bv = w64 str)
    by (rewrite (fsw_reg_extra (w_H W) regs _ ssT ms 9%bv 1 HS ltac:(vm_compute; reflexivity)); reflexivity).
  (* the frame region of the call state: its chunks, read on the call memory *)
  lazymatch eval vm_compute in (nth_error (ss_mem ssT) 0) with
  | Some ?r0 => pose proof (fsw_region_nth E ssT _ 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
  end.
  cbn [ms_mem restrict] in HR0. unfold YP09.region_ok in HR0.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR0.
  rewrite E2 in HR0. destruct HR0 as (_ & _ & _ & HC0).
  pose proof (proj1 (Forall_forall _ _) HC0) as CK. clear HC0.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). change (ss_pc ssT) with PC_strlen.
  eapply SRr_bind.
  { apply (fsw_intrin_atU B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W (ms_mem ms) mdT 0 U (fun a => spZ regs - 192 - STK_RT_STR <= a < spZ regs - 192)
      (w64 (raZ (ms_regs ms))) _
      (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
         (exists v0, getr regs' 10 = w64 v0 /\ 0 <= v0 < 2 ^ 64 /\ v0 = Z.of_nat (length txt)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
            aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)) HJ).
    - eapply SRr_mono; [exact (HSLEN ly S U W (ms_regs ms) (ms_mem ms) mdT str txt HPRET HROMT R10T HCSOKT)|].
      intros W' c' _ Hp.
      destruct (wv_rt_post_conv STK_RT_STR ly S U W (ms_regs ms) (ms_mem ms) mdT _ W' c' HUOK Hp)
        as (-> & regs' & mem' & md' & Ec & HARU' & Hsbm & Hfr & Hprs & HQ).
      split; [reflexivity|]. exists regs', mem', md'. split; [exact Ec|]. split; [exact HARU'|]. split; [exact Hsbm|].
      split; [intros a Ha Hn; apply Hfr; [exact Ha | rewrite SPT; exact Hn]|].
      split; [exact Hprs | exact HQ].
    - intros a Ha. left. left. lia. }
  intros W2 c2 Hle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v2 & G10' & Hv2 & Ev2) & Hfr2).
  (* ---- the resume at 0x843c8: a sub-journal at the entry sp, the frame reloaded from the call memory ---- *)
  pose proof (ajournal_sub_init tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_write_value (2 - k)) (spZ regs) []
    (spZ regs - ot) HJ2 ltac:(lia) ltac:(rewrite Zminus_mod, Hsp16, Hot16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))
    as J3.
  assert (SP2 : spZ regs2 = spZ regs - 192).
  { unfold spZ. rewrite (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). exact SPT. }
  assert (E3sp : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ wv_xsR regs str kids keys n d)) 2) = spZ regs - 192)
    by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact SP2).
  assert (HS3 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ wv_xsR regs str kids keys n d))
    (fss_retT 0x843c8 192 wv_cs0 [] []) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x843c8) mem2 (seg_rom tfibsegs)))).
  { apply (fsw_resume_after_rtU_args B (STK_write_value (2 - k)) (spZ regs) [] ly S W (unpoison U mem2) md2 [] ly S U W
      mem2 md2 0 (ms_regs ms) regs2 (ms_mem ms) 192 (wv_xsR regs str kids keys n d) wv_cs0 [] [] 0x843c8 HBgot HBcell J3
      HARU2 HP2).
    - exact SPT.
    - lia.
    - lia.
    - reflexivity.
    - vm_compute. reflexivity.
    - cbv [wv_cs0 map seq Nat.add]. repeat constructor; cbn; lia.
    - cbv [wv_cs0 map seq Nat.add].
      repeat match goal with
      | |- Forall _ [] => constructor
      | |- Forall _ (YP09.mkChunk ?off2 (CVal 8 ?e2) :: _) =>
          let o1 := eval vm_compute in (off2 - 192) in
          constructor;
          [ eapply (wv_chunk_move E _ _ (spZ regs) (spZ regs - 192) o1 off2 _ e2);
            [ apply CK; cbn [In]; repeat (first [left; reflexivity | right])
            | lia
            | lazymatch goal with
              | |- sv_denot _ (SOff 32 0) = _ =>
                  rewrite !fsw_SOff0; change 32%nat with (32 + 0)%nat; subst E; rewrite !ew_Ereg_extra; reflexivity
              | |- sv_denot _ (SOff (xatom ?j) 0) = sv_denot _ (SOff ?r 0) =>
                  rewrite !fsw_SOff0, fsw_ew_xatom; subst E;
                  cbn [nth wv_xsR wv_xs app map wv_saved];
                  symmetry; apply ew_Ereg_nat; vm_compute; reflexivity
              end ]
          | ]
      end.
    - intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. rewrite SPT. lia.
    - constructor.
    - apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E3sp.
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - exact I. }
  assert (ER : w64 (raZ (ms_regs ms)) = Z_to_bv 64 0x843c8)
    by (unfold raZ, w64; rewrite R1T; apply Z_to_bv_bv_unsigned).
  rewrite ER.
  fsw_aj_run_toU fsw_wr_tbl_ok HS3 J3 HARU2 A_put.
  + (* the epilogue writes only the frame *)
    cbv [fss_retT fsT_ret_regions ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -192);
      [reflexivity | first [exact E3sp | match goal with |- ?g => idtac "AWRG" g end; fail]
      | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  + (* ---- at the tail jump to put (0x84440 j 0x8449c) ---- *)
    lazymatch goal with HS3 : st_ok _ _ ?ssf (restrict _ ?m) |- _ => set (ssJ2 := ssf) in HS3; rename m into msJ end.
    lazymatch goal with HFJ0 : frame_of _ (ss_mem (fss_retT _ _ _ _ _)) mem2 (ms_mem msJ) |- _ => rename HFJ0 into HFJ end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdJ := mdx) in * end.
    pose proof HARU2 as (_ & OK3 & PO3).
    destruct (fsw_rt_atU B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W mem2 md2 0 (STK_write_value (2 - k)) (spZ regs) [] [] ly S U W (ms_mem msJ) mdJ 0
      HJ2 J3 OK3 PO3 ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as [HJJ _].
    cbn [app] in HJJ. rewrite Z.add_0_r in HJJ.
    assert (HMJ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value (2 - k) <= a < spZ regs) ->
      mbyte tfibsegs (rdW W (ms_mem msJ)) a = mbyte tfibsegs (rdW W mem) a).
    { intros a Ha Hn.
      assert (EA : mbyte tfibsegs (rdW W (ms_mem msJ)) a = mbyte tfibsegs (rdW W mem2) a).
      { unfold mbyte, mrestrict.
        rewrite (wv_frameR _ 0x843c8 wv_cs0 mem2 (ms_mem msJ) (spZ regs) HFJ E3sp); [reflexivity|].
        rewrite (wz a Ha). lia. }
      assert (EB : mbyte tfibsegs (rdW W mem2) a = mbyte tfibsegs (rdW W (ms_mem ms)) a).
      { apply (mbyte_of_aview tfibsegs). apply Hfr2; [exact Ha|]. rewrite SPT. lia. }
      assert (EC : mbyte tfibsegs (rdW W (ms_mem ms)) a = mbyte tfibsegs (rdW W mem) a).
      { unfold mbyte, mrestrict. rewrite (wv_frame0 E _ _ _ mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
        rewrite (wz a Ha). lia. }
      rewrite EA, EB, EC. reflexivity. }
    assert (HPJ : aregs_preserved regs (ms_regs msJ)).
    { apply (fsw_preserved (w_H W) _ ssJ2 msJ regs (sr_get (ss_regs ssJ2)) HS3); [vm_compute; reflexivity|].
      fsw_cs_cases (sr_get (ss_regs ssJ2)) HS HP2 E3sp. }
    assert (R1J : getr (ms_regs msJ) 1%bv = getr regs 1%bv).
    { rewrite (fsw_reg_extra (w_H W) regs2 _ ssJ2 msJ 1%bv 18 HS3 ltac:(vm_compute; reflexivity)).
      cbn [nth fs_extraT app wv_xsR wv_xs map wv_saved]. reflexivity. }
    assert (G10J : getr (ms_regs msJ) 10%bv = w64 o).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 10%bv 8%bv 8%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)), R8T. exact G10. }
    assert (G11J : getr (ms_regs msJ) 11%bv = w64 str).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 11%bv 9%bv 9%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 9%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)), R9T. reflexivity. }
    assert (G12J : getr (ms_regs msJ) 12%bv = w64 (Z.of_nat (length txt))).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 12%bv 10%bv 10%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite G10', Ev2. reflexivity. }
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msJ HS3 eq_refl).
    change (ss_pc ssJ2) with A_put.
    pose proof HCS as (_ & Hlen & (Hbytes & _)).
    pose proof HCSOK0 as ((Hg & _) & _ & Hceil' & _).
    apply (wv_tail_put B HPUT (2 - k) ly S U W regs mem md ch ot o v pretty d (PjTree.JNum txt bits) D UL buf cap failed text
      live peak cnt fail (ms_regs msJ) (ms_mem msJ) mdJ str txt HPRE HHEADS HFRL HOUT HGLOB HUH Hspo Hoot Hot16 Hottop
      HCHO HPRESENT HN HPO HUL HD Hroot eq_refl).
    * cbn [WriterValue.wvpieces concat] in HROOM. rewrite app_nil_r in HROOM. exact HROOM.
    * exact HCAP.
    * exact HCL.
    * exact HBUD.
    * exact (wv_garr8_prefix _ _ _ _ Hg).
    * right; left. exists str, kk. split; [exact Hne|]. split; [exact HRB|]. split; [lia | lia].
    * unfold WriterSpec.bytes_ok. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia.
    * (* 0 <= str: Hs1 reads 4096 + HEAD <= str, and lia keeps the constant HEAD opaque *)
      cbv [HEAD] in Hs1. lia.
    * lia.
    * exact HJJ.
    * exact HARU2.
    * exact HMJ.
    * exact HPJ.
    * exact R1J.
    * exact G10J.
    * exact G11J.
    * exact G12J.
Qed.
End W.
