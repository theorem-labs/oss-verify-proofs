(* check_as_written, the tail of the inlined expected_body (fs.c:96, `r = m % 4; if ( *text || pad > 2 || r == 1 ||
   (r == 2 && (six[m-1] & 15)) || (r == 3 && (six[m-1] & 3))) n = SIZE_MAX;`), fs.asan 0x81724 .. 0x817dc / 0x8197c:
   from the scan loop's exit the walk either refuses (n = SIZE_MAX, pc 0x8197c, the `jal __wrap_free` of six) or
   accepts and enters the emit loop (pc 0x817dc), or accepts with m = 0 and goes straight to 0x8197c with n = 0.
   This is `WriterSpec.b64_dec`'s `(pad <=? 2) && six_tail_ok six` (lib/Prog/WriterSpec.v:105-114).
   Ported from: donor proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (token walk form) and a Theorem Labs lane
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_check_as_written.v (branch / run tactic shape), a working branch
   42af91cff3b -> proofs/omx-clap-core/fuzz_state/lib/A/FSW_caw_tail.v. Control flow after fs's RELEASED plain proof
   lib/Prog/check_as_written.v:200.
   Section hypotheses: none (this segment calls nothing; it only runs instrumented program code). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_caw_defs FSW_caw_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic state at 0x81724 (the scan loop's single exit) ----
   atoms: 31 RA (FSW_caw_defs.v caw_regs1: ra is an atom, no contract pins it to 0x815f8; no segment reads it),
   33 six, 34 want, 35 the text pointer the scan stopped at, 37 the byte there, 38 m, 39 pad,
   40 six + m (alias), 43 six[m - 1], 50-61 scratch *)
Definition cawt_regs : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-48); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 53 0; SOff 54 0; SOff 38 0; SOff 39 0;
   SOff 55 0; SOff 56 0; SOff 57 0;
   SOff 34 0; SOff 35 0; SOff 32 0;
   SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 58 0; SOff 59 0; SOff 60 0; SOff 61 0].
Definition cawt_txt : YP09.region :=
  YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition cawt_six : YP09.region :=
  YP09.mkRegion (Some 40%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 43 0))].
Definition cawt_facts (blo bhi plo phi : Z) : facts :=
  mkFacts [(37%nat, mkAF blo bhi 0);
           (39%nat, mkAF plo phi 0);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 CAW_CEIL 0);
           (34%nat, mkAF 4096 CAW_CEIL 0);
           (35%nat, mkAF 4096 CAW_CEIL 0);
           (38%nat, mkAF 0 3145728 0);
           (40%nat, mkAF 4096 CAW_CEIL 0);
           (43%nat, mkAF 0 63 0)]
          []
          [(SAlu ALU_ADD (SOff 33 0) (SOff 38 0), SOff 40 0)].
(* without the six[m - 1] byte (m may be 0 there) and with it (m >= 1, the r = 2 / r = 3 arms) *)
Definition cawt_ss (blo bhi plo phi : Z) : sstate :=
  mkSS 0x81724 cawt_regs [caw_stk; cawt_txt] None (cawt_facts blo bhi plo phi).
Definition cawt_SH : list shent := [mkSHE 35 0 1].
Definition cawt_K : nat := Eval vm_compute in run_K 0 caw_Bx cawt_SH (cawt_ss 0 255 0 2147483647).


(* the state at 0x8197c (`jal __wrap_free` of six) on the refusal arm: s3 = SIZE_MAX, a0 = six, s2 = want
   (MEASURED: the engine's state after the run from 0x81724 with a nonzero byte at the pointer) *)
Definition cawt_regs_free (a2v : Z) : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-48); SOff 3 0; SOff 4 0;
   SOff 50 0; SOff 51 0; SOff 52 0;
   SOff 12 0; SOff 11 0; SOff 33 0; SLit 1; SLit a2v;
   SOff 38 0; SOff 63 0; SOff 55 0; SOff 56 0; SOff 57 0;
   SOff 34 0; SLit 18446744073709551615; SOff 32 0;
   SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 58 0; SOff 59 0; SOff 60 0; SOff 61 0].
Definition cawt_facts_free (blo bhi plo phi : Z) : facts :=
  mkFacts ((39%nat, mkAF plo phi 0) :: (37%nat, mkAF blo bhi 0) :: f_atoms (cawt_facts 0 255 0 2147483647))
          (f_conds (cawt_facts 0 255 0 2147483647)) (f_alias (cawt_facts 0 255 0 2147483647)).
(* a2 holds the byte test (snez), the two first facts the arm's byte / pad ranges *)
Definition cawt_ss_free (a2v blo bhi plo phi : Z) : sstate :=
  mkSS 0x8197c (cawt_regs_free a2v) [caw_stk; cawt_txt] None (cawt_facts_free blo bhi plo phi).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable Q : world tfibsegs -> config -> Prop.

(* st_ok with one more atom fact (YP06 add_atom / facts_ok_add_atom) *)
Lemma cawt_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
      (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms n f HS Hf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))) | exact Hf].
Qed.

(* `andi a1, a3, 3` is m mod 4 *)
Lemma cawt_and3 : forall E n m, ew E n = w64 m -> 0 <= m < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 3)) = m mod 4.
Proof.
intros E n m Hn Hm. rewrite U_and_lit by lia. rewrite U_SOff, Hn, Z.add_0_r.
unfold w64. rewrite unsigned_lit_small by exact Hm. rewrite (zcanon_id m) by (unfold M64; lia).
replace 3 with (Z.ones 2) by reflexivity. rewrite Z.land_ones by lia. reflexivity.
Qed.

(* ---- the refusal arm: the byte at the pointer where the scan stopped is not the NUL (the scan broke on a
   character the grammar refuses; plain check_as_written_c.v:25, b64_dec = None) ---- *)
Lemma cawt_refuse_byte : forall E ms mdc ly S U (W : world tfibsegs) STK sp0 ly0 S0 W0 mem0 md0 k bt pad,
  st_ok tfibsegs E (cawt_ss 0 255 0 2147483647) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B ly S U W (ms_mem ms) mdc ->
  sh_ok tfibsegs caw_Bx cawt_SH E (mrestrict (w_H W) (ms_mem ms)) ->
  ew E 37 = w64 bt -> 1 <= bt <= 255 -> ew E 39 = w64 pad -> 0 <= pad <= 2 ->
  bv_unsigned (ew E 2) = sp0 -> 48 <= STK ->
  (forall E' ms' mdc',
     (forall n, (n < 62)%nat -> ew E' n = ew E n) ->
     st_ok tfibsegs E' (cawt_ss_free 1 1 255 0 2) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
       ly S W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B ly S U W (ms_mem ms') mdc' ->
     sh_ok tfibsegs caw_Bx cawt_SH E' (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc ly S U W STK sp0 ly0 S0 W0 mem0 md0 k bt pad HS HJ HARU SHOK E37 Hbt E39 Hpad Esp HSTK HCONT.
pose proof (cawt_add_atom E _ _ 37%nat (mkAF 1 255 0) HS
  ltac:(split; [rewrite E37; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss cawt_facts f_atoms f_conds f_alias] in HS1.
clear HS.
pose proof (cawt_add_atom _ _ _ 39%nat (mkAF 0 2 0) HS1
  ltac:(split; [rewrite E39; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS2.
clear HS1. rename HS2 into HS1.
fsw_aj_run_to_tokU caw_tbl_ok HS1 HJ HARU SHOK caw_Bspan 0x8197c.
- (* the run writes only the frame window of check_as_written *)
  cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat).
  { reflexivity. }
  { exact Esp. }
  { cbn. lia. }
  { cbn. lia. }
  { apply awr_ok_cons_ro. { cbn. lia. } { apply awr_ok_nil. } }
- apply (HCONT (ewset (ewset E 62 w) 63 w0) ms0 (with_vm_backing (m_vm_lazy mdc) mat mdc));
    [intros n Hn; rewrite !ew_ewset_other by lia; reflexivity
    | unfold cawt_ss_free, cawt_regs_free, cawt_facts_free, cawt_facts; exact HS1
    | exact HJ | exact HARU | exact SHOK].
Qed.

(* ---- the refusal arm the scan reaches with BOTH a refused character and more than two '=' (e.g. the text
   "===A": b64_scan takes three pads and then refuses the sextet, so the walk arrives at 0x81724 with a nonzero
   byte AND pad >= 3). The two arms above each fix the other value, so neither covers it; the code refuses here
   for the same reason as cawt_refuse_byte (`snez a2` of the nonzero byte makes `or a1, a2, a1` 1 whatever the
   pad flag is), and the run is the same one. ---- *)
Lemma cawt_refuse_byte_pad : forall E ms mdc ly S U (W : world tfibsegs) STK sp0 ly0 S0 W0 mem0 md0 k bt pad,
  st_ok tfibsegs E (cawt_ss 0 255 0 2147483647) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B ly S U W (ms_mem ms) mdc ->
  sh_ok tfibsegs caw_Bx cawt_SH E (mrestrict (w_H W) (ms_mem ms)) ->
  ew E 37 = w64 bt -> 1 <= bt <= 255 -> ew E 39 = w64 pad -> 3 <= pad <= 2147483647 ->
  bv_unsigned (ew E 2) = sp0 -> 48 <= STK ->
  (forall E' ms' mdc',
     (forall n, (n < 62)%nat -> ew E' n = ew E n) ->
     st_ok tfibsegs E' (cawt_ss_free 1 1 255 3 2147483647) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
       ly S W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B ly S U W (ms_mem ms') mdc' ->
     sh_ok tfibsegs caw_Bx cawt_SH E' (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc ly S U W STK sp0 ly0 S0 W0 mem0 md0 k bt pad HS HJ HARU SHOK E37 Hbt E39 Hpad Esp HSTK HCONT.
pose proof (cawt_add_atom E _ _ 37%nat (mkAF 1 255 0) HS
  ltac:(split; [rewrite E37; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss cawt_facts f_atoms f_conds f_alias] in HS1.
clear HS.
pose proof (cawt_add_atom _ _ _ 39%nat (mkAF 3 2147483647 0) HS1
  ltac:(split; [rewrite E39; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS2.
clear HS1. rename HS2 into HS1.
fsw_aj_run_to_tokU caw_tbl_ok HS1 HJ HARU SHOK caw_Bspan 0x8197c.
- cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat).
  { reflexivity. }
  { exact Esp. }
  { cbn. lia. }
  { cbn. lia. }
  { apply awr_ok_cons_ro. { cbn. lia. } { apply awr_ok_nil. } }
- apply (HCONT (ewset (ewset E 62 w) 63 w0) ms0 (with_vm_backing (m_vm_lazy mdc) mat mdc));
    [intros n Hn; rewrite !ew_ewset_other by lia; reflexivity
    | unfold cawt_ss_free, cawt_regs_free, cawt_facts_free, cawt_facts; exact HS1
    | exact HJ | exact HARU | exact SHOK].
Qed.

(* ---- the refusal arm: the scan reached the NUL but more than two '=' were read (plain check_as_written_c.v:25;
   b64_dec's `pad <=? 2` false) ---- *)
Lemma cawt_refuse_pad : forall E ms mdc ly S U (W : world tfibsegs) STK sp0 ly0 S0 W0 mem0 md0 k pad,
  st_ok tfibsegs E (cawt_ss 0 255 0 2147483647) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B ly S U W (ms_mem ms) mdc ->
  sh_ok tfibsegs caw_Bx cawt_SH E (mrestrict (w_H W) (ms_mem ms)) ->
  ew E 37 = w64 0 -> ew E 39 = w64 pad -> 3 <= pad <= 2147483647 ->
  bv_unsigned (ew E 2) = sp0 -> 48 <= STK ->
  (forall E' ms' mdc',
     (forall n, (n < 62)%nat -> ew E' n = ew E n) ->
     st_ok tfibsegs E' (cawt_ss_free 0 0 0 3 2147483647) (restrict (w_H W) ms') ->
     ajournal tfibsegs B STK sp0 [] ly0 S0 W0 (unpoison U mem0) md0 []
       ly S W (unpoison U (ms_mem ms')) mdc' k ->
     ARU tfibsegs B ly S U W (ms_mem ms') mdc' ->
     sh_ok tfibsegs caw_Bx cawt_SH E' (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros E ms mdc ly S U W STK sp0 ly0 S0 W0 mem0 md0 k pad HS HJ HARU SHOK E37 E39 Hpad Esp HSTK HCONT.
pose proof (cawt_add_atom E _ _ 37%nat (mkAF 0 0 0) HS
  ltac:(split; [rewrite E37; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts cawt_ss cawt_facts f_atoms f_conds f_alias] in HS1.
clear HS.
pose proof (cawt_add_atom _ _ _ 39%nat (mkAF 3 2147483647 0) HS1
  ltac:(split; [rewrite E39; unfold w64; rewrite unsigned_lit_small by lia; cbn [af_lo af_hi]; lia|];
        split; [cbn [af_al2]; rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | cbn [af_al2]; lia])) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS2.
clear HS1. rename HS2 into HS1.
fsw_aj_run_to_tokU caw_tbl_ok HS1 HJ HARU SHOK caw_Bspan 0x8197c.
- cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat).
  { reflexivity. }
  { exact Esp. }
  { cbn. lia. }
  { cbn. lia. }
  { apply awr_ok_cons_ro. { cbn. lia. } { apply awr_ok_nil. } }
- apply (HCONT (ewset (ewset E 62 w) 63 w0) ms0 (with_vm_backing (m_vm_lazy mdc) mat mdc));
    [intros n Hn; rewrite !ew_ewset_other by lia; reflexivity
    | unfold cawt_ss_free, cawt_regs_free, cawt_facts_free, cawt_facts; exact HS1
    | exact HJ | exact HARU | exact SHOK].
Qed.

End W.
