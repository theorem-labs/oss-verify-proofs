(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x807c8, listing offset 0x90) on the ASan build of libreac
   v1.9.0: its first phase, pe_E, in the form PcapEntryPhases.v fixes for the harness walks:
     pe_from POST GI_K1 -> pe_from POST GI_leave -> pe_start POST
   (PcapEntryTop.v's Section top hypothesis pe_E at PI := PI_pcap, KS := pcap_KS, POST := pe_post).

   The walk (every number from the original v1.9.0 pin fuzz_pcap.asan, sha256 b7a91d9b1fb0017d...;
   symbols from its unstripped twin fuzz_pcap.asan (sha256 36da3052c383); capstone disassembly):
     R1  0x807c8 .. 0x80838: the 224-byte machine frame, the probe and the 13 saves (0x807cc .. 0x80800), s0 := sp0,
         sp := s1 := (sp0 - 224) & -32 (0x80808, 0x8080c), the use-after-return flag (GOT 0x99888 -> 0xa18c0) and the
         shadow base (GOT 0x99830 -> 0xa18b8), beqz a2 0x80830 decided by the flag's value 1 (AR_const_law), a0 := 0x80.
     __asan_stack_malloc_1 (jal 0x80838, return 0x8083c): YC85G.aj_stack_malloc_atS on the gx journal's inner donor
         journal, repacked with W_journalG.ajournal_gx_pack; the class-1 frame F (fpos) and its flag pointer.
     R2  0x8083c .. 0x808f0: bnez s4 0x8084c decided by F >= 4096 (so the machine-frame arm 0x80850..0x80868 is not
         run), the slot 0x70(s1) := F, the header (magic, objects 5 and 6) and the 16 shadow bytes PSH_entry.
     0x808f0 bnez a1 (a1 = size >> 26, 0x808bc): the early return to PP_leave is NOT taken, refuted from pe_base's
         size bound c_n < 2^26 (pe_U_srl); the premise for GI_leave is therefore not used.
     0x808f4 beqz s3: split on the size.
       size = 0 (R3, 0x8091c ..): s6 := 0, slot 0x20(s1) := 0.
       size > 0 (R3, 0x808f8 ..): the shadow check of the first input byte (srli / add / lb 0x80900, bnez 0x80904 to
         the slow block 0x81348, whose blt 0x8134c returns to 0x80908) is decided by the shadow token [c_p, c_p + 1),
         from AR's shadow law over the caller's input block (YCbq.range_addressable_of_block), so the report call
         0x81354 (__asan_report_load1) is never reached; lbu 0x80908 reads d; slot 0x20(s1) := d, s5 := input + 1,
         s6 := size - 1.
       both: g_file := s5 (0x80930), slot 0x40(s1) := the auipc value 8 (0x80934), g_file_len := s6 (0x80938),
         a0 := s6, jal malloc 0x80940.
     malloc (0x80940, return PP_K1 0x80944): pe_E_malloc, PaJournalFs.amalloc04_sub_fs on the inner donor journal
         (PcapHarnessA.h_B_malloc's form); its room from pe_base (LIVE_LIB, pe_need), its result >= 4096.

   Section hypotheses (each the exact type of the fact it stands for; the composer discharges them):
     LAWS   AR_laws SEGS B                      the core's allocator laws (cgif core)
     TL     PALib B                             the listing's runtime symbols (PcapPaLib.v)
     TLF    PALibF B                            __asan_stack_malloc_1's entry and the GOT / cell separation (PcapFrame.v)
     MTL    ameter_laws MT                      the meter (row 11: YCbp.ameter_triv_laws)
     MFSL   ameter_fs_laws MT                   the meter ignores the frame state (row 11: YCbp's trivial meter)
     ML     model_laws (as_universe B)          the allocator model (YG05.model_laws_ok; as PcapHarnessTail.v's ML)
     ASM1   astack_malloc_realizes SEGS B 1     the side-stack entry for class 1 (YG0d.v, cgif core)
     AM     amalloc04_rule SEGS B MT            malloc's rule (YC5d.v, cgif core)
     ASIL   asource_img_laws SK SEGS B KS       the stream symbols' image laws (PSourceMeta.v)
     HGLEN  VAL (A_HI 8) + 0x618 = VAL (A_OBJ 4)  PcapEntryTop.pi_pcap_glen (as PcapHarnessA.v's HGLEN)
   The facts about the harness's globals pe_G (no stream env byte in pe_G, pe_G writable, g_file_len below g_file)
   come from pe_base (PcapEntryDefs.v:404, :406, :409; a working branch 9be46202615). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YImgTop YE00 YE01 YG0p YC5d YI13.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 YC88 PcapFrame PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapHarnessA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- generic helpers, copied from a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v (a working branch
   f0d76b020fe, lines 300-367), which took them from cgif_file_fuzzer lib/A/ACer.v:24-25, 86-91, 131-139, 156-164
   (origin/ossv/recipes c8557374ad2e). ---- *)
Lemma pe_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma pe_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite pe_land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.

Lemma pe_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)) as Hle. pose proof (Z.div_pos (v + c) 32 ltac:(lia) ltac:(lia)) as Hp.
assert (HU : U E (SAlu ALU_AND (SOff n c) (SLit (-32))) = 32 * ((v + c) / 32)).
{ unfold U. rewrite (pe_denot_and_m32 E n v c Hn H0 H1 Hv). apply unsigned_lit_small. lia. }
rewrite HU. apply zcanon_id. rewrite M64_val. lia.
Qed.

Definition pe_chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
  Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition pe_trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
    (filter (pe_chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint pe_trim_stack (rs : smem) (lo hi : Z) : smem :=
  match rs with
  | [] => []
  | r :: t => match YP09.r_base r with
              | Some 2%nat => pe_trim_region r lo hi :: t
              | _ => r :: pe_trim_stack t lo hi end end.
Ltac pe_subregion_tac :=
  unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
  let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
  first [exact Hc | solve [destruct Hc] | tauto].
Ltac pe_submem_to := repeat (first [apply submem_keep; [pe_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac pe_norm_pi HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let v := eval vm_compute in ss in change ss with v in HS end.
(* A register's symbolic value, not normalized (prreg normalizes it). *)
Ltac pe_prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac pe_add_fact HS n f prf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_pi_add_fact Ev ssx msx n f HS ltac:(prf)) as HS3; clear HS; rename HS3 into HS; pe_norm_pi HS end.

(* The shift-right of a 64-bit value by a literal (a Theorem Labs lane's GrantEntryHead.v gh_U_srl, a working branch
   b83b8251684, generic over the engine's sv; copied, renamed). *)
Lemma pe_U_srl : forall E x k, 0 <= k < 64 -> U E (SAlu ALU_SRL x (SLit k)) = U E x / 2 ^ k.
Proof.
intros E x k Hk. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k
  by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (U_range E x) as Hr. unfold M64 in *.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : U E x / 2 ^ k <= U E x).
{ apply Z.div_le_upper_bound; [exact Hp|].
  assert (H1 : 1 <= 2 ^ k) by (rewrite <- (Z.pow_0_r 2); apply Z.pow_le_mono_r; lia).
  rewrite Z.mul_comm. rewrite <- (Z.mul_1_r (U E x)) at 1. apply Z.mul_le_mono_nonneg_l; lia. }
assert (Hge : 0 <= U E x / 2 ^ k) by (apply Z.div_pos; lia).
revert Hle Hge. generalize (U E x / 2 ^ k). intros q Hle Hge.
apply zcanon_id. unfold M64. lia.
Qed.
(* A region of an st_ok state, by index (a Theorem Labs lane's PcapSourceOpen.v sregion, a working branch). *)
Ltac pe_sregion HS i HR :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let o := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch o with Some ?r =>
      pose proof (st_ok_region_nth (segs:=segs) E ss (restrict H ms) i r HS ltac:(vm_compute; reflexivity)) as HR;
      cbn [ms_mem restrict mkst] in HR end end.
(* The regions with base atom n made read-only (their chunks kept). *)
Definition pe_ro (n : nat) (rs : smem) : smem :=
  map (fun r => if YP09.obase_eqb (YP09.r_base r) (Some n)
                then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r) else r) rs.
(* A callee-saved register of the ABI (PcapHarnessA.v's section-local acs, which is not visible outside its section;
   restated). *)
Ltac pe_acs := unfold acallee_saved; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
  | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
  | right; right; right; right; right; split; vm_compute; discriminate].

(* ---- the symbolic state at the first slot (0x807c8) ---- *)
(* Atoms: 0..31 the entry registers, 32 the shadow offset SB, A_TEXT.. the listing's image values. The regions: the
   224-byte machine frame below sp (0x807c8 addi sp,sp,-0xe0; written by the probe 0x807cc and the 13 saves
   0x807d0..0x80800), the GOT word of the shadow-base cell (object 1) and the cell (object 15), the GOT word of the
   use-after-return flag (object 0) and the flag (object 16, a 4-byte 1: AR_const_law). *)
Definition pe_regions0 : smem :=
  [stack_region PE_MFRAME; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 16); uar_cell_regionP (A_OBJ 16)].
Definition pe_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_pe0 : sstate := mkSS PP_entry sr_atoms pe_regions0 None pe_facts0.
Definition pe_extra : list word := [Z_to_bv 64 SB].
(* The regions the body writes after __asan_stack_malloc_1 (0x8083c..0x80940): the spill slots s1 + [0, 120)
   (0x70(s1) 0x8086c, 0x20(s1) 0x8090c / 0x80920, 0x40(s1) 0x80934; atom 60 = s1), g_file (object 2, 8 bytes:
   sd s5,0(s2) 0x80930) and g_file_len (the auipc value 8 + 0x618, 8 bytes: sd s6,0x618(a1) 0x80938). *)
Definition pe_rS1 : YP09.region := YP09.mkRegion (Some 60%nat) 0 120 0 120 [].
Definition pe_rG2 : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 8 [].
Definition pe_rG4 : YP09.region := YP09.mkRegion (Some (A_HI 8)) PE_GLEN_LO PE_GLEN_LO8 PE_GLEN_LO PE_GLEN_LO8 [].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is EXPLICIT on every lemma of this file (a Theorem Labs lane, 21:57Z), as in PcapHarnessA.v. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- reading the engine's regions back (a Theorem Labs lane's GrantEntryHead.v, a working branch b83b8251684:
   gh_cbyte, gh_chunks_match, gh_shadow_bytes, gh_cword, gh_word_of_region, gh_word_at; copied, renamed pe_*, over
   PAImg pcap_listing) ---- *)
Definition pe_cbyte (cs : list YP09.chunk) (i : Z) : option Z :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with
              | CVal w v => if N.eqb w 1 then match v with SLit z => Some (zcanon z mod 256) | _ => None end
                            else None
              | _ => None end
  | None => None
  end.
Definition pe_chunks_match (cs : list YP09.chunk) (sh : list Z) : bool :=
  forallb (fun i => match pe_cbyte cs (Z.of_nat i) with Some v => Z.eqb v (nth i sh 0) | None => false end)
          (seq 0 (length sh)).
Definition pe_cword (cs : list YP09.chunk) (i : Z) : option sv :=
  match find (fun c => Z.eqb (YP09.c_off c) i) cs with
  | Some c => match YP09.c_val c with CVal w v => if N.eqb w 8 then Some v else None | _ => None end
  | None => None
  end.

Lemma pe_shadow_bytes : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs sh,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  pe_chunks_match cs sh = true ->
  forall i, (i < length sh)%nat -> aview SEGS H m (base + Z.of_nat i) = Some (nth i sh 0).
Proof.
intros E H m nn base lo hi wlo whi cs sh Hr Hb Hm i Hi.
unfold pe_chunks_match in Hm. rewrite forallb_forall in Hm.
specialize (Hm i ltac:(apply in_seq; lia)).
destruct (pe_cbyte cs (Z.of_nat i)) as [v|] eqn:Hc; [|discriminate Hm].
apply Z.eqb_eq in Hm.
unfold pe_cbyte in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) (Z.of_nat i)) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct (YP09.c_val c) as [w z| | |] eqn:Hv; try discriminate Hc.
destruct (N.eqb w 1) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw. subst w.
destruct z as [zz| | | | | | | | | |]; try discriminate Hc.
injection Hc as <-.
destruct Hr as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs c Hin) as Hck.
cbn [YP09.r_base YP09.base_val] in Hck. rewrite Hb in Hck.
specialize (Hck 0 ltac:(unfold YP09.c_len; rewrite Hv; cbn [YP09.cv_len]; lia)).
destruct Hck as (b & Hcb & Hmb).
rewrite Hv in Hcb. cbn [YP09.cbyte] in Hcb. injection Hcb as <-.
rewrite Hoff, Z.add_0_r in Hmb.
unfold aview. rewrite Hmb. cbn [option_map]. f_equal. rewrite <- Hm.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (bv_modulus 64) with (2 ^ 64). unfold zcanon, M64. reflexivity.
Qed.

Lemma pe_word_of_region : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hin He Hv.
apply (rdword_of_val_mem SEGS H m); [|exact Hv].
change 8%nat with (N.to_nat 8).
exact (field_of_region E (mrestrict H m) nn base cs lo hi wlo whi off 8%N e v Hr Hb Hin He
  ltac:(cbn [Z.of_N]; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma pe_word_at : forall E (H : word -> bool) (m : word -> option byte) nn base lo hi wlo whi cs off e v,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E nn) = base ->
  pe_cword cs off = Some e ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (base + off) = Some v.
Proof.
intros E H m nn base lo hi wlo whi cs off e v Hr Hb Hc He Hv.
unfold pe_cword in Hc.
destruct (find (fun c => Z.eqb (YP09.c_off c) off) cs) as [c|] eqn:Hf; [|discriminate Hc].
destruct (find_some _ _ Hf) as [Hin Hoff]. apply Z.eqb_eq in Hoff.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Hoff, Hc, Hin.
destruct cv as [w z| | |]; try discriminate Hc.
destruct (N.eqb w 8) eqn:Hw; [|discriminate Hc]. apply N.eqb_eq in Hw.
injection Hc as Hc. subst w. subst co. subst z.
exact (pe_word_of_region E H m nn base lo hi wlo whi cs off _ v Hr Hb Hin He Hv).
Qed.

(* The 13 saved words of the machine frame, read back from the stack region (GrantEntryHead.v gh_saved_of). *)
Lemma pe_saved_of : forall E (H : word -> bool) (m : word -> option byte) sp0 (regs : bvmap 5 word)
  lo hi wlo whi cs,
  YP09.region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2%nat) = sp0 ->
  (forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r) ->
  pe_cword cs (-8) = Some (SOff 1%nat 0) ->
  pe_cword cs (-16) = Some (SOff 8%nat 0) ->
  pe_cword cs (-24) = Some (SOff 9%nat 0) ->
  pe_cword cs (-32) = Some (SOff 18%nat 0) ->
  pe_cword cs (-40) = Some (SOff 19%nat 0) ->
  pe_cword cs (-48) = Some (SOff 20%nat 0) ->
  pe_cword cs (-56) = Some (SOff 21%nat 0) ->
  pe_cword cs (-64) = Some (SOff 22%nat 0) ->
  pe_cword cs (-72) = Some (SOff 23%nat 0) ->
  pe_cword cs (-80) = Some (SOff 24%nat 0) ->
  pe_cword cs (-88) = Some (SOff 25%nat 0) ->
  pe_cword cs (-96) = Some (SOff 26%nat 0) ->
  pe_cword cs (-104) = Some (SOff 27%nat 0) ->
  rdword (aview SEGS H m) (sp0 - 8) = Some (bv_unsigned (getr regs 1%bv)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS H m) (sp0 - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
Proof.
intros E H m sp0 regs lo hi wlo whi cs Hr Hb HEE K1 K8 K9 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27.
assert (W1 : forall (nn : nat) (r : bv 5) off e,
  Z.of_nat nn = bv_unsigned r -> e = SOff nn 0 -> pe_cword cs off = Some e ->
  rdword (aview SEGS H m) (sp0 + off) = Some (bv_unsigned (getr regs r))).
{ intros nn r off e Hn He Hc. subst e.
  apply (pe_word_at E H m 2%nat sp0 lo hi wlo whi cs off (SOff nn 0) _ Hr Hb Hc); [|apply u64_range].
  cbn [sv_denot]. rewrite (HEE nn r Hn), Z.add_0_r. reflexivity. }
split.
- replace (sp0 - 8) with (sp0 + -8) by lia. exact (W1 1%nat 1%bv (-8) _ eq_refl eq_refl K1).
- intros j Hj.
  assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9
               \/ j = 10 \/ j = 11) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]]]]]];
  [ replace (sp0 - 16 - 8 * 0) with (sp0 + -16) by lia
  | replace (sp0 - 16 - 8 * 1) with (sp0 + -24) by lia
  | replace (sp0 - 16 - 8 * 2) with (sp0 + -32) by lia
  | replace (sp0 - 16 - 8 * 3) with (sp0 + -40) by lia
  | replace (sp0 - 16 - 8 * 4) with (sp0 + -48) by lia
  | replace (sp0 - 16 - 8 * 5) with (sp0 + -56) by lia
  | replace (sp0 - 16 - 8 * 6) with (sp0 + -64) by lia
  | replace (sp0 - 16 - 8 * 7) with (sp0 + -72) by lia
  | replace (sp0 - 16 - 8 * 8) with (sp0 + -80) by lia
  | replace (sp0 - 16 - 8 * 9) with (sp0 + -88) by lia
  | replace (sp0 - 16 - 8 * 10) with (sp0 + -96) by lia
  | replace (sp0 - 16 - 8 * 11) with (sp0 + -104) by lia ];
  cbn [Z.ltb Z.compare Z.add];
  [ exact (W1 8%nat (8%bv : bv 5) (-16) _ eq_refl eq_refl K8)
  | exact (W1 9%nat (9%bv : bv 5) (-24) _ eq_refl eq_refl K9)
  | exact (W1 18%nat (18%bv : bv 5) (-32) _ eq_refl eq_refl K18)
  | exact (W1 19%nat (19%bv : bv 5) (-40) _ eq_refl eq_refl K19)
  | exact (W1 20%nat (20%bv : bv 5) (-48) _ eq_refl eq_refl K20)
  | exact (W1 21%nat (21%bv : bv 5) (-56) _ eq_refl eq_refl K21)
  | exact (W1 22%nat (22%bv : bv 5) (-64) _ eq_refl eq_refl K22)
  | exact (W1 23%nat (23%bv : bv 5) (-72) _ eq_refl eq_refl K23)
  | exact (W1 24%nat (24%bv : bv 5) (-80) _ eq_refl eq_refl K24)
  | exact (W1 25%nat (25%bv : bv 5) (-88) _ eq_refl eq_refl K25)
  | exact (W1 26%nat (26%bv : bv 5) (-96) _ eq_refl eq_refl K26)
  | exact (W1 27%nat (27%bv : bv 5) (-104) _ eq_refl eq_refl K27) ].
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MFSL : ameter_fs_laws MT.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis AM : amalloc04_rule SEGS B MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis HGLEN : VAL (A_HI 8) + PE_GLEN_LO = VAL (A_OBJ 4).

(* __asan_stack_malloc's progress, from the model laws. *)
Let SMP : stack_malloc_progressP B := fun s cid HW Hc Hn => ml_stack_malloc_progress _ ML s cid HW Hc Hn.
Let BR := paj_branch (PI := PI).

Lemma pe_entry0 : forall cx, pe_base SK B MT KS cx ->
  st_ok_pi SEGS VAL (Eimg (Ereg (c_regs cx) pe_extra)) ss_pe0
    (restrict (w_H (c_W cx)) (mkst (c_regs cx) (Z_to_bv 64 (BASE + PP_entry)) (c_mem cx) (seg_rom SEGS))).
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & _ & H11 & Hpn & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
pose proof (pa_obj_img 15 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 0 ltac:(lia)) as HguarR. pose proof (pa_obj_img 16 ltac:(lia)) as HuarR.
unfold pcap_img_end, YImgTop.IMG_TOP in HcellR, HgotR, HguarR, HuarR.
pose proof (palf_sep B TLF) as Hsep. rewrite (pal_uar_cell B TL) in Hsep. cbn [zseps zseps_from fst snd] in Hsep.
set (E := Eimg (Ereg (c_regs cx) pe_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (c_regs cx) pe_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr (c_regs cx) 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (c_regs cx) _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 (c_n cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (c_regs cx) _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 0)).
assert (EIMG : forall i, (i < 17)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (VBI : forall i, (i < 17)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EIMG i Hi) | pose proof (pa_val_range (A_OBJ i)); lia]. }
rewrite restrict_mkst_fx. unfold ss_pe0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pe_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, PE_MFRAME.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
  + fold E. rewrite (VBI 1%nat ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15)));
    [cbn [sv_denot]; rewrite (EIMG 15%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 15)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kgot).
  + fold E. rewrite (VBI 15%nat ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 15)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kcell).
  + fold E. rewrite (VBI 0%nat ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 16) 0) (VAL (A_OBJ 16)));
    [cbn [sv_denot]; rewrite (EIMG 16%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 16)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kguar).
  + fold E. rewrite (VBI 16%nat ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 16)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H (c_W cx)) (c_mem cx) _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold pe_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, PE_MFRAME,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite !VBI by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold LLVMF_STK in *.
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HcellR HgotR HguarR HuarR Hsep.
  clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pe_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, E11, E32, !unsigned_lit_small by (unfold SB; lia).
  try change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  unfold LLVMF_STK in *.
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hsp0al Hn26.
  clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- the malloc of the copy (jal 0x80940, malloc(size - 1), malloc(0) for an empty input) and its return to PP_K1
   (0x80944): the call state as the walk leaves it, the allocator rule amalloc04_rule lifted by
   PaJournalFs.amalloc04_sub_fs on the gx journal's inner donor journal (PcapHarnessA.h_B_malloc's form) ---- *)
Lemma pe_E_malloc : forall POST, pe_from SK B MT KS POST (GI_K1 B MT KS) ->
  forall cx fp k acc ly3 S3 W3 (ms : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) md3 k ->
  frames S3 = [(PE_CID, fp)] -> mo_le MT (c_S cx) S3 acc -> k <= 0 -> acc <= 0 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) ->
  m_fds md3 = m_fds (c_md cx) -> m_fs md3 = m_fs (c_md cx) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PP_K1) -> getr (ms_regs ms) 2 = w64 (c_sp1 cx) ->
  getr (ms_regs ms) 3 = getr (c_regs cx) 3 -> getr (ms_regs ms) 4 = getr (c_regs cx) 4 ->
  getr (ms_regs ms) 8 = w64 (spZ (c_regs cx)) -> getr (ms_regs ms) 9 = w64 (c_sp1 cx) ->
  getr (ms_regs ms) 10 = w64 (p_nF cx) -> getr (ms_regs ms) 18 = w64 (VAL (A_OBJ 2)) ->
  getr (ms_regs ms) 20 = w64 (pF cx fp) -> getr (ms_regs ms) 21 = w64 (p_src cx) ->
  getr (ms_regs ms) 22 = w64 (p_nF cx) -> getr (ms_regs ms) 23 = w64 (pF cx fp) ->
  getr (ms_regs ms) 25 = w64 (pSH cx fp) -> getr (ms_regs ms) 27 = w64 SHADOW_OFF ->
  psaved cx W3 ms -> pheader cx fp W3 ms -> pshadow cx fp W3 ms PSH_entry ->
  garr8 SEGS (rdW W3 (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  pslot cx W3 ms PS_D (p_d cx) -> pslot cx W3 ms PS_GLEN (VAL (A_HI 8)) -> pslot cx W3 ms PS_F0 (pF cx fp) ->
  p_glob cx W3 ms (p_src cx) -> asource_none SEGS KS (rdW W3 (ms_mem ms)) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (pc_wrap_malloc (as_code B))) (ms_mem ms) (seg_rom SEGS)) md3)
    (POST cx).
Proof.
  intros POST HK1 cx fp k acc ly3 S3 W3 ms md3 HB HJ HFR HMO Hk Hacc HPERM Hfds Hfs
    Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q18 Q20 Q21 Q22 Q23 Q25 Q27 HSAVED HHDR HSH HIN SD SGLEN SF0 HGL HNONE.
  pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
  destruct (h_base SK B MT KS cx HB) as (HROD & HMETA & HG & HGR).
  destruct HJ as (_ & _ & (memS & HJm & HAGm) & _). rewrite !Z.add_0_r in HJm.
  pose proof (h_frame SK B MT KS LAWS cx fp memS ly3 S3 W3 (ms_mem ms) md3 k HB HJm HFR)
    as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJm as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
  pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
  pose proof (p_d_range cx) as Hd.
  pose proof HB as ((_ & _ & Hra4 & Hgp0 & Htp0 & _) & _ & _ & _ & HINP & _ & _ & Hnev0 & Hlive0 & _ & _ & _ & _ & _ & _ &
                    _ & HMOK & Hneed & _ & _ & _ & HTRm & HTRf).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct HINP as [[-> _] | [Hn _]]; lia).
  assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HSHr : SB + 512 <= pSH cx fp /\ pSH cx fp + 16 <= SB + 2 ^ 44 /\ pSH cx fp mod 8 = 0).
  { destruct (h_div8_of_mul64 (pF cx fp) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
    pose proof (Z.div_lt_upper_bound (pF cx fp + 128) 8 (2 ^ 44)
      ltac:(clear - HFapp C1 C3; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia) ltac:(lia)).
    pose proof (Z.div_le_lower_bound (pF cx fp) 8 512 ltac:(lia) ltac:(lia)).
    replace ((pF cx fp + 128) / 8) with (pF cx fp / 8 + 16) in H
      by (rewrite <- (Z.div_add (pF cx fp) 16 8) by lia; f_equal; lia).
    split; [lia|]. split; [lia|].
    rewrite E8. replace (2147450880 + 8 * (pF cx fp / 64)) with ((268431360 + pF cx fp / 64) * 8) by lia.
    apply Z_mod_mult. }
  unfold SB in HSHr.
  assert (DFSH : pF cx fp + 128 <= pSH cx fp \/ pSH cx fp + 16 <= pF cx fp)
    by (clear - HFapp HSHr C1 C3; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
  assert (Esp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2; apply h_w64_unsigned; lia).
  assert (Es0 : s0Z (ms_regs ms) = spZ (c_regs cx)) by (unfold s0Z; rewrite Q8; apply h_w64_unsigned; lia).
  pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HBok.
  assert (Era : raZ (ms_regs ms) = BASE + PP_K1).
  { unfold raZ. rewrite Q1, unsigned_lit_small; [reflexivity|]. unfold PP_K1. lia. }
  (* the room of the call: the copy is at most size - 1 < 2^26 bytes (LIVE_LIB), its meter at most PA_K1 *)
  assert (Hbb : blocks_bytes S3 + p_nF cx <= LIVE_MAX).
  { rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ HPERM).
    rewrite <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). unfold LIVE_LIB in *. unfold c_n in Hn26.
    unfold p_nF in *. lia. }
  assert (Hmo : mo_ok MT S3 (mo_malloc MT (p_nF cx))).
  { pose proof (PA_K12_need MT MTL cx) as HN.
    pose proof (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as N1.
    pose proof (mo_malloc_nonneg MT MTL (p_bn cx) ltac:(lia)) as N2.
    pose proof (mo_free_nonneg MT MTL) as N3.
    apply (mo_ok_le MT MTL S3 _ (c_T cx - acc)); [|unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1 in *; lia].
    apply (mo_ok_step MT MTL (c_S cx) S3 acc (c_T cx - acc)); [|exact HMO].
    replace (acc + (c_T cx - acc)) with (c_T cx) by lia. exact HMOK. }
  eapply SRr_bind.
  { eapply (amalloc04_sub_fs SK SEGS B LAWS pa_segs_low MT AM W3 (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx))
      [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(PE_CID, fp)] ly3 S3 md3 k (p_nF cx)
      (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + PP_K1)) (pch cx) HJm Q10).
    - unfold MALLOC_MAX. unfold p_nF, c_n in *. lia.
    - exact Hbb.
    - rewrite Esp. lia.
    - replace (c_sp1 cx - spZ (c_regs cx)) with ((c_sp1 cx / 16 - spZ (c_regs cx) / 16) * 16)
        by (pose proof (h_mod32_8 _ Hsp1_32) as [M16 _]; pose proof (Z_div_mod_eq_full (c_sp1 cx) 16);
            pose proof (Z_div_mod_eq_full (spZ (c_regs cx)) 16); lia).
      apply Z.mod_mul. lia.
    - lia.
    - unfold ASTACK, LLVMF_STK. lia.
    - rewrite Q3. exact Hgp0.
    - rewrite Q4. exact Htp0.
    - exact Q1.
    - apply ret_ok_codeptr_v; [unfold PP_K1; lia | reflexivity].
    - unfold EV_LIB in *. lia.
    - apply (achain_chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (pch cx) (ms_regs ms)).
      + apply (h_achain SK B MT KS cx memS ly3 S3 W3 (ms_mem ms) md3 [(PE_CID, fp)] k (c_sp1 cx) HB HJm HAGm).
        * exact (proj1 HSAVED).
        * pose proof (proj2 HSAVED 0 ltac:(lia)) as HS0. rewrite Z.mul_0_r, Z.sub_0_r in HS0. exact HS0.
        * lia.
      + rewrite Esp. lia.
      + exact Es0.
      + rewrite Era. unfold PP_K1. lia.
    - apply HTRm. rewrite Era. replace (BASE + PP_K1 - BASE) with 0x20c by (unfold PP_K1; lia). cbn. left. reflexivity.
    - exact Hmo. }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & res & Ec & HJ2 & HPR & Hres & Hfr2 & Hr4 & Hbl & HK & MLE &
                                Hfd2 & Hfs2).
  subst c2. destruct HK as (K1 & K2 & K3 & K4 & _ & _).
  pose proof HJ2 as (HAR2 & Hly2 & _).
  assert (EF2 : frame_addr ly2 PE_CID fp = pF cx fp).
  { pose proof HB as ((HAR0 & _) & _). destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & Efa & _).
    unfold pF. apply Efa. }
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in K1 by lia.
  assert (Hnew : In (res, p_nF cx) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (Hfresh : ~ In (res, p_nF cx) (ablocks B ly3 S3)).
  { pose proof (h_ablocks_nodup B LAWS ly2 S2 W2 mem2 md2 HAR2) as Hnd. rewrite Hbl in Hnd.
    exact (h_nodup_app_disj _ _ _ _ Hnd (or_introl eq_refl)). }
  assert (Hfin2 : In (PE_CID, fp) (frames S2)) by (rewrite Hfr2; exact Hfin).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hnew Hfin2) as Dnew.
  rewrite EF2 in Dnew. change (fs_frame_bytes PE_CID) with 128 in Dnew.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hnew) as (_ & _ & Hnceil & Hnapp & _ & _ & _).
  pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [_ Hreqn].
  (* what the call kept: the caller's blocks, the frame and its shadow, the stack above the call's window, the image *)
  assert (KB : forall p m i, In (p, m) (ablocks B ly3 S3) -> 0 <= i < req_size m ->
     aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W3) (ms_mem ms) (p + i)).
  { intros p m i Hin Hi.
    assert (Hin2 : In (p, m) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hin).
    assert (Hne : (p, m) <> (res, p_nF cx)) by (intros E'; apply Hfresh; rewrite <- E'; exact Hin).
    pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hin2 Hnew Hne) as D.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
    rewrite (K2 p m i Hin Hi); [reflexivity|]. cbn beta. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
  assert (KF : forall a, (pF cx fp <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. rewrite (K4 PE_CID fp a Hfin); [reflexivity | |].
    - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr; cbn [frame_rng fst snd];
        [rewrite EF; change (fs_frame_bytes PE_CID) with 128; lia|].
      replace (shadow_addr (frame_addr ly3 PE_CID fp)) with (pSH cx fp) by (rewrite EF, ESH; unfold shadow_addr; reflexivity).
      change (fs_frame_bytes PE_CID / 8) with 16. lia.
    - cbn beta. unfold zdisjoint in Dnew. cbn [fst snd] in Dnew.
      clear - Ha Dnew Hnapp HFapp HSHr C1 C3 Hreqn.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hnapp, HFapp. lia. }
  assert (KH : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Ha. rewrite K1; [reflexivity | lia | lia]. }
  assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
  { intros a Hi Hns Her. rewrite (K3 a Hi Hns Her). reflexivity. }
  apply (HK1 cx fp (k + 1) (acc + mo_malloc MT (p_nF cx)) ly2 S2 W2
           (mkst regs2 (Z_to_bv 64 (BASE + PP_K1)) mem2 (seg_rom SEGS)) md2 HB).
  { eapply (ajournal_gx_pack (SK := SK)); [unfold LLVMF_STK; lia | lia | | exact HAGm | intros a Ha _; lia].
    rewrite (Z.add_0_r LLVMF_STK), (Z.add_0_r (spZ (c_regs cx))). exact HJ2. }
  { rewrite Hfr2. exact HFR. }
  { exact (mo_le_trans MT MTL _ _ _ _ _ HMO MLE). }
  exists res.
  split.
  { unfold p_cut. split.
    2:{ split; [lia|]. split; [unfold PA_K1; lia|].
        split; [rewrite Hbl; apply Permutation_app_tail; exact HPERM|].
        split; [rewrite Hfd2, Hfds; reflexivity | rewrite Hfs2, Hfs; reflexivity]. }
    unfold pe_body, pregs, psaved, pheader, pshadow.
    cbn [ms_mem ms_regs ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { rewrite !(h_pres _ _ _ HPR) by pe_acs.
      split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q27|]. split; [exact Q3 | exact Q4]. }
    split.
    { split.
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KH; lia | exact (proj1 HSAVED)].
      - intros j Hj. apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KH; lia|].
        exact (proj2 HSAVED j Hj). }
    split.
    { destruct HHDR as (HH0 & HH8 & HH16 & HH120).
      split; [|split; [|split]].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KF; lia | exact HH0].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KF; lia | exact HH8].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KF; lia | exact HH16].
      - apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KF; unfold PE_FLAGPTR; lia | exact HH120]. }
    split; [intros i Hi; rewrite KF; [exact (HSH i Hi) | change (length PSH_entry) with 16%nat in Hi; lia]|].
    split; [reflexivity|].
    { apply (garr8_frame SEGS (rdW W3 (ms_mem ms)) (rdW W2 mem2) _ _ HIN). intros a Ha. rewrite length_map in Ha.
      apply (mbyte_of_aview SEGS).
      destruct HINP as [(Hn0 & _) | (Hn & Hinc)]; [unfold c_n in Hn0; lia|].
      assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hinc).
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqp].
      unfold c_n in *. replace a with (c_p cx + (a - c_p cx)) by lia. apply (KB _ _ _ Hin3). lia. } }
  cbn [ms_mem ms_regs mkst].
  split; [exact Hn26|]. split; [exact Hr4|]. split; [exact Hres|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q18|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q20|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q21|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q22|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q23|].
  split; [rewrite (h_pres _ _ _ HPR) by pe_acs; exact Q25|].
  unfold pslot in SD, SGLEN, SF0.
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KH; unfold PS_D; lia | exact SD]|].
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KH; unfold PS_GLEN; lia | exact SGLEN]|].
  split; [unfold pslot; apply (h_rdword_keep (w_H W3) (w_H W2) (ms_mem ms) mem2); [intros i Hi; apply KH; unfold PS_F0; lia | exact SF0]|].
  split.
  { unfold p_glob, pval in *. destruct HGL as (HGL2 & HGL4). split.
    - eapply vm_frame_segs; [|exact HGL2]. intros x Hx. apply (mbyte_of_aview SEGS).
      assert (Hin : inG pe_G x) by (apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
        change (Z.of_nat 8) with 8 in Hx; lia).
      destruct (HG x Hin) as [Hi Hns]. destruct (HGR x Hin) as (_ & _ & Her & _). exact (KI x Hi Hns Her).
    - eapply vm_frame_segs; [|exact HGL4]. intros x Hx. apply (mbyte_of_aview SEGS).
      assert (Hin : inG pe_G x) by (apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; change (Z.of_nat 8) with 8 in Hx; lia).
      destruct (HG x Hin) as [Hi Hns]. destruct (HGR x Hin) as (_ & _ & Her & _). exact (KI x Hi Hns Her). }
  { apply (asource_none_frame_segs SEGS KS (rdW W3 (ms_mem ms)) (rdW W2 mem2)); [|exact HNONE].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hns & Her). exact (KI a Hi Hns Her). }
Qed.

Theorem pe_E : forall POST, pe_from SK B MT KS POST (GI_K1 B MT KS) -> pe_from SK B MT KS POST (GI_leave B MT KS) ->
  pe_start SK B MT KS POST.
Proof.
intros POST HK1 HLV cx HB.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (h_sp SK B MT KS cx HB) as (Hsp16 & Hsp_lo & Hsp_hi & Hsp1 & Hsp1_32).
destruct (h_base SK B MT KS cx HB) as (HROD & HMETA & HG & HGR).
pose proof HB as (HPRE & Hra & H10 & H11 & Hpn & HPL & Hfr0 & Hev0 & Hlive0 & _ & Hnone & Hhead & _ & Hsp1d & _ & _ &
                  HMOK & Hneed & _ & _ & _ & HTRm & HTRf).
(* pe_base's facts on the harness's globals, through PcapHarnessA's h_base / h_base_objsep (PcapEntryDefs.v:404, :406,
   :409). *)
pose proof (h_base_objsep SK B MT KS cx HB) as HGSEP.
assert (HGENV : forall a, inG pe_G a -> ~ asrc_env_addr KS a)
  by (intros a Ha; destruct (HGR a Ha) as (_ & _ & _ & _ & Henv & _); exact Henv).
assert (GX_W : forall a, inG pe_G a -> forall m, writable_at SEGS m a)
  by (intros a Ha; destruct (HGR a Ha) as (_ & _ & _ & _ & _ & Hw); exact Hw).
pose proof HPRE as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hn26 : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
pose proof (pe_entry0 cx HB) as HS.
pose proof (ajournal_gx_init (SK := SK) SEGS B pe_G 0 [] LLVMF_STK [sink_token] _ _ _ _ _ _ _ HPRE ltac:(lia) ltac:(reflexivity)
  ltac:(unfold LLVMF_STK in *; lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg (c_regs cx) pe_extra)) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (c_regs cx) pe_extra) n)
  by (intros nn Hn'; subst E; apply Eimg_low; exact Hn').
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (c_regs cx) r)
  by (intros q r Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (c_regs cx) _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ (c_regs cx)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (rdW (c_W cx) (c_mem cx))) by constructor.
clear HEdef.
change (w64 (BASE + PP_entry)) with (Z_to_bv 64 (BASE + PP_entry)).
pose (RUNX := paj_run_x (SK := SK) B LAWS pe_G HG 0 []).
(* ---- R1: the prologue up to the call of __asan_stack_malloc_1 (0x80838) ---- *)
paj_run_tok RUNX HS HJ SHOK hBspan0.
{ apply awr_ok_x_of0.
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (c_regs cx) - 224 <= a < spZ (c_regs cx)) ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ apply (kept_of_frame (segs := SEGS) E (ss_mem ss_pe0) (w_H (c_W cx)) (c_mem cx) (ms_mem ms) _ HFr).
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?Usp in Ha; clear - Ha; lia |]).
  destruct Hin. }
clear HF HFr.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (2%bv : bv 5) R2.
assert (Esp0 : ew E 2 = Z_to_bv 64 (spZ (c_regs cx)))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hsp1v : c_sp1 cx = 32 * ((spZ (c_regs cx) + -224) / 32))
  by (rewrite Hsp1d; unfold pe_sp1, PE_MFRAME; replace (spZ (c_regs cx) + -224) with (spZ (c_regs cx) - 224) by lia;
      reflexivity).
(* s1 = sp = (sp0 - 224) & -32 (0x80808 andi, 0x8080c mv) *)
assert (Rsp1 : getr (ms_regs ms) 2 = Z_to_bv 64 (c_sp1 cx)).
{ rewrite R2.
  change (alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (ew E 2) + -224)) (Z_to_bv 64 (-32)))
    with (sv_denot E (SAlu ALU_AND (SOff 2 (-224)) (SLit (-32)))).
  rewrite (pe_denot_and_m32 E 2 (spZ (c_regs cx)) (-224) Esp0) by lia. rewrite Hsp1v. reflexivity. }
(* The machine frame trimmed to the 13 saves (sp0 - 104 .. sp0); the GOT words and the cells are not read again. *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (pe_trim_stack rs (-104) 0) [0]%nat) in
  pose proof (st_ok_submem SEGS Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; pe_submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* ---- __asan_stack_malloc_1(0x80) at 0x80838, on the gx journal's inner donor journal ---- *)
(* Its window is ESTACK = 4096 below s1: ESTACK - (s1 - sp0) <= 4096 + 240 <= LLVMF_STK = 32768. *)
rewrite (palf_sm1 B TLF).
destruct HJ as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
{ destruct (h_mod32_8 _ Hsp1_32) as [M16 _]. rewrite Zminus_mod, M16, Hsp16. reflexivity. }
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS (SK := SK) SEGS B LAWS Hsegs (pal_env B TL) ML SMP 1 ASM1 ltac:(lia) (c_W cx) (ms_regs ms) (ms_mem ms)
    LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [] (c_ly cx) (c_S cx) _ 0
    (c_sp1 cx - spZ (c_regs cx)) _ HJi).
  - unfold spZ at 1. rewrite Rsp1, unsigned_lit_small by lia. lia.
  - exact Ho16.
  - lia.
  - change ESTACK with 4096. unfold LLVMF_STK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HK & HJe & (fS2 & ES2)).
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK, HJe by lia. change ESTACK with 4096 in HK.
destruct (ajournal_closed_fs SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJe) as [Efd2 Efs2].
rewrite (proj1 (wvb_fds_fs _ _ _)) in Efd2. rewrite (proj2 (wvb_fds_fs _ _ _)) in Efs2.
rewrite Hfr0 in Hfrs2.
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof (h_frame SK B MT KS LAWS cx fpos memS (c_ly cx) S2 (c_W cx) mem2 md2 0 HB HJ2 Hfrs2)
  as (EF & EFL & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HSHpres).
assert (HJg2 : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
  (c_mem cx) (c_md cx) [(PE_CID, fpos)] (c_ly cx) S2 (c_W cx) mem2 md2 0).
{ apply (ajournal_gx_pack (SK := SK) SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fpos)] (c_ly cx) S2 (c_W cx) mem2 md2 0 memS);
  [unfold LLVMF_STK; lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact HAG | intros a Ha _; lia]. }
jafter_call_keep_pi HS 40%nat regs2 (rdW (c_W cx) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). pose proof HK as (K1 & _). apply K1; lia.
  - intros _. apply (apresent_writable SEGS). apply Hpres2. unfold LLVMF_STK. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
clear HE1.
(* The frame F (a0 after the call, atom 44), its flag FL and its shadow SH = SB + F / 8. *)
change (frame_addr (c_ly cx) 1 fpos) with (pF cx fpos) in Ha0, Hflag, Hz.
change (flag_addr (c_ly cx) 1 fpos) with (pFL cx fpos) in Hflag.
change (fs_frame_bytes 1) with 128 in Hflag, Hz.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 (pF cx fpos)) by (rewrite <- R10, Ha0; reflexivity). clear R10.
assert (HSHr : SB + 512 <= pSH cx fpos /\ pSH cx fpos + 16 <= SB + 2 ^ 44 /\ pSH cx fpos mod 8 = 0).
{ destruct (h_div8_of_mul64 (pF cx fpos) HF64) as [E8 E64]. rewrite ESH. unfold SHADOW_OFF, SB.
  pose proof (Z.div_lt_upper_bound (pF cx fpos + 128) 8 (2 ^ 44) ltac:(clear - HFapp C1 C3; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia) ltac:(lia)).
  pose proof (Z.div_le_lower_bound (pF cx fpos) 8 512 ltac:(lia) ltac:(lia)).
  replace ((pF cx fpos + 128) / 8) with (pF cx fpos / 8 + 16) in H
    by (rewrite <- (Z.div_add (pF cx fpos) 16 8) by lia; f_equal; lia).
  split; [lia|]. split; [lia|].
  rewrite E8. replace (2147450880 + 8 * (pF cx fpos / 64)) with ((268431360 + pF cx fpos / 64) * 8) by lia.
  apply Z_mod_mult. }
assert (DFSH : pF cx fpos + 128 <= pSH cx fpos \/ pSH cx fpos + 16 <= pF cx fpos)
  by (clear - HFapp HSHr C1 C3; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 ltac:(rewrite Hfrs2; left; reflexivity)) as (_ & _ & HFLapp & HFLlt).
change (flag_addr (c_ly cx) 1 fpos) with (pFL cx fpos) in HFLapp, HFLlt.
(* s1 and sp: rebound to the atom 60 = s1 (the engine places no store through a masked address). *)
assert (E12 : ew Ev1 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact Esp0).
pe_prreg_raw HS (2%bv : bv 5) Rsp2. pe_prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (pe_denot_and_m32 Ev1 2 (spZ (c_regs cx)) (-224) E12) in Rsp2 by lia.
rewrite (pe_denot_and_m32_add0 Ev1 2 (spZ (c_regs cx)) (-224) E12) in Rs12 by lia.
rewrite <- Hsp1v in Rsp2, Rs12.
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (pFL cx fpos); Z_to_bv 64 (pSH cx fpos)] HS
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (pFL cx fpos); Z_to_bv 64 (pSH cx fpos)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 60)%nat -> ew E3v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E3v 60 = Z_to_bv 64 (c_sp1 cx))
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (pFL cx fpos); Z_to_bv 64 (pSH cx fpos)]
        0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E61 : ew E3v 61 = Z_to_bv 64 (pFL cx fpos))
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (pFL cx fpos); Z_to_bv 64 (pSH cx fpos)]
        1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (pSH cx fpos))
  by (rewrite HE3; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 (c_sp1 cx); Z_to_bv 64 (pFL cx fpos); Z_to_bv 64 (pSH cx fpos)]
        2 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI3 : img_env VAL A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE3.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
assert (E3_2 : ew E3v 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD3 by lia; exact E12).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SB) by (rewrite OLD3, OLD1 by lia; exact E32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 (pF cx fpos)) by (rewrite OLD3 by lia; exact E44).
assert (E3_62 : ew E3v 62 = Z_to_bv 64 (SB + pF cx fpos / 8)) by (rewrite E62, ESH, <- SB_SHADOW_OFF; reflexivity).
assert (U60 : bv_unsigned (ew E3v 60) = c_sp1 cx) by (rewrite E60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = pF cx fpos) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = pSH cx fpos) by (rewrite E62; apply unsigned_lit_small; unfold SB in HSHr; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ (c_regs cx)) by (rewrite E3_2; apply unsigned_lit_small; lia).
assert (UG2 : bv_unsigned (ew E3v (A_OBJ 2)) = VAL (A_OBJ 2))
  by (rewrite (img_env_atomP E3v (A_OBJ 2) HEI3) by (unfold A_OBJ, A_TEXT, A_LIM; lia); apply unsigned_lit_small;
      apply pa_val_range).
assert (UG8 : bv_unsigned (ew E3v (A_HI 8)) = VAL (A_HI 8))
  by (rewrite (img_env_atomP E3v (A_HI 8) HEI3) by (unfold A_HI, A_TEXT, A_LIM; lia); apply unsigned_lit_small;
      apply pa_val_range).
pose proof UG2 as UG2n. pose proof UG8 as UG8n.
lazymatch type of UG2n with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG2n end.
lazymatch type of UG8n with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG8n end.
pose proof (pa_obj_img 2 ltac:(lia)) as HO2. pose proof (pa_obj_img 4 ltac:(lia)) as HO4.
unfold pcap_img_end, YImgTop.IMG_TOP in HO2, HO4.
pe_add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32;
        repeat split; lia).
pe_add_fact HS 44%nat (HPTR 6)
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E3_44, unsigned_lit_small by lia; change (2 ^ 6) with 64;
        repeat split; lia).
pe_add_fact HS 62%nat (mkAF SB (SB + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E62, unsigned_lit_small by (unfold SB in HSHr; lia);
        change (2 ^ 3) with 8; unfold SB in *; repeat split; lia).
pe_add_fact HS (A_OBJ 2) (mkAF 65536 (symaddr ImgPages.Asan.top) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite UG2; rewrite ?Z.pow_0_r, ?Z.mod_1_r; repeat split; lia).
pe_add_fact HS (A_HI 8) (mkAF 0 (symaddr ImgPages.Asan.top) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite UG8; rewrite ?Z.pow_0_r, ?Z.mod_1_r; repeat split; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS
    (shadow_decl_ok Ev 44 32 62 (pF cx fpos) SB E3_44 ltac:(lia) E3_32 E3_62)) as HS3 end.
clear HS; rename HS3 into HS; pe_norm_pi HS.
(* The frame's shadow as __asan_stack_malloc_1 leaves it: 16 zero bytes (zero_shadow). *)
assert (ZB : forall i, 0 <= i < 16 -> mbyte SEGS (rdW (c_W cx) mem2) (pSH cx fpos + 0 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold zero_shadow in Hz. pose proof (Hz i ltac:(change (128 / 8) with 16; lia)) as Hzi.
  change (shadow_of_addr SHADOW_OFF (pF cx fpos)) with (pSH cx fpos) in Hzi.
  destruct (aview_byte SEGS _ _ _ _ Hzi) as (bb & Hbb & Hv & _).
  rewrite Z.add_0_r. rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity. }
assert (HFLb : 0 <= pFL cx fpos < alloc_ceiling)
  by (clear - HFLapp HFLlt C1; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp; lia).
assert (HFa : pF cx fpos + 128 <= kLowShadowBeg \/ kHighMemBeg <= pF cx fpos)
  by (clear - HFapp; unfold in_app in HFapp; lia).
pose proof HFimg as HFo. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo.
(* The five regions the rest of the walk writes: s1's slots, the frame (header 0..24, flag pointer at 120), its
   16 shadow bytes, g_file, g_file_len. *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ pe_rS1 HS eq_refl
  ltac:(unfold region_ok, pe_rS1; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable SEGS); apply Hpres2; unfold LLVMF_STK; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, pe_rS1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite U60, U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply HFpres; lia
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS _ _ (pF cx fpos) 120 8 _ (pFL cx fpos));
          [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (pF cx fpos + 120) with (pF cx fpos + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region, pe_rS1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        change (fs_frame_bytes 1) with 128; rewrite U60, U44, U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 1 0 16 [YP09.mkChunk 0 (CZero 16)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold SB in HSHr; lia|]; split; [unfold SB in HSHr; lia|]; split;
        [ intros o Ho; apply (apresent_writable SEGS); apply HSHpres; lia
        | apply Forall_cons; [apply chunk_ok_zero; exact ZB | apply Forall_nil] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region, pe_rS1; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; rewrite U60, U44, U62, U3_2;
        unfold SB in HSHr; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
assert (IG2 : forall a, VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8 -> inG pe_G a)
  by (intros a Ha; unfold inG, pe_G; apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
assert (IG4 : forall a, VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8 -> inG pe_G a)
  by (intros a Ha; unfold inG, pe_G; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ pe_rG2 HS eq_refl
  ltac:(unfold region_ok, pe_rG2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite UG2; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply GX_W; apply IG2; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region, pe_rS1, pe_rG2;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; rewrite U60, U44, U62, U3_2, ?UG2, ?UG2n;
        unfold SB in HSHr; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ pe_rG4 HS eq_refl
  ltac:(unfold region_ok, pe_rG4; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite UG8; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply GX_W; apply IG4; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region, pe_rS1, pe_rG2, pe_rG4;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; rewrite U60, U44, U62, U3_2, ?UG2, ?UG2n, ?UG8, ?UG8n;
        unfold SB in HSHr; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; pe_norm_pi HS.
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E3v (rdW (c_W cx) mem2)) by constructor.
assert (EE3 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E3v nn = getr (c_regs cx) r).
{ intros nn r Hn. pose proof (bv_unsigned_in_range 5 r) as Hb5. change (bv_modulus 5) with 32 in Hb5.
  rewrite OLD3, OLD1 by lia. exact (EE nn r Hn). }
assert (EG2 : ew E3v (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (apply (img_env_atomP E3v (A_OBJ 2) HEI3); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG5 : ew E3v (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5)))
  by (apply (img_env_atomP E3v (A_OBJ 5) HEI3); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG6 : ew E3v (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
  by (apply (img_env_atomP E3v (A_OBJ 6) HEI3); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG8 : ew E3v (A_HI 8) = Z_to_bv 64 (VAL (A_HI 8)))
  by (apply (img_env_atomP E3v (A_HI 8) HEI3); unfold A_HI, A_TEXT, A_LIM; lia).
pose (Zw2 := fun a => (VAL (A_OBJ 4) <= a < VAL (A_OBJ 4) + 8) \/ (VAL (A_OBJ 2) <= a < VAL (A_OBJ 2) + 8) \/
  (pSH cx fpos <= a < pSH cx fpos + 16) \/ (pF cx fpos <= a < pF cx fpos + 128) \/
  (c_sp1 cx <= a < c_sp1 cx + 120) \/ (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx))).
(* ---- R2: the frame's header (0x80898..0x808a0) and its 16 shadow bytes (0x808ac..0x808ec), up to the early-return
   test 0x808f0 ---- *)
paj_run_tok RUNX HS HJg2 SHOK2 hBspan0.
{ apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG8, ?UG8n in Ha. apply IG4. lia. }
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG2, ?UG2n in Ha. apply IG2. lia. }
  apply awr_ok_x_of0.
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 62%nat (pSH cx fpos)); [reflexivity | exact U62 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr (c_ly cx) PE_CID fpos)) with (pSH cx fpos).
    change (fs_frame_bytes PE_CID / 8) with 16. lia. }
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 44%nat (pF cx fpos)); [reflexivity | exact U44 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (c_ly cx) PE_CID fpos) with (pF cx fpos). change (fs_frame_bytes PE_CID) with 128. lia. }
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite U3_2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw2 a ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms0) a = aview SEGS (w_H (c_W cx)) mem2 a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ _ HFr) end.
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha;
    rewrite ?U60, ?U44, ?U62, ?U3_2, ?UG2n, ?UG8n in Ha; unfold Zw2; clear - Ha HGLEN; lia |]).
  destruct Hin. }
clear HF HFr.
assert (E3_11 : ew E3v 11 = Z_to_bv 64 (c_n cx))
  by (rewrite OLD3, OLD1 by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11).
(* 0x808f0 bnez a1 (a1 = size >> 26, 0x808bc): the early return of an input of 2^26 bytes or more is NOT taken, since
   pe_base bounds the input below 2^26; the premise for PP_leave is not needed. *)
psrr_branch_tok RUNX BR HS SHOK2 hBspan0.
{ exfalso. rewrite branch_ne_U in Hc. rewrite (pe_U_srl _ _ 26 ltac:(lia)) in Hc.
  rewrite (U_atom _ 11%nat (c_n cx) E3_11) in Hc by lia. rewrite (U_lit _ 0) in Hc by lia.
  rewrite (Z.div_small (c_n cx) (2 ^ 26)) in Hc by lia. cbn in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUNX HS HJg2 SHOK2 hBspan0.
{ apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG8, ?UG8n in Ha. apply IG4. lia. }
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG2, ?UG2n in Ha. apply IG2. lia. }
  apply awr_ok_x_of0.
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 62%nat (pSH cx fpos)); [reflexivity | exact U62 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr (c_ly cx) PE_CID fpos)) with (pSH cx fpos).
    change (fs_frame_bytes PE_CID / 8) with 16. lia. }
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 44%nat (pF cx fpos)); [reflexivity | exact U44 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (frame_addr (c_ly cx) PE_CID fpos) with (pF cx fpos). change (fs_frame_bytes PE_CID) with 128. lia. }
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite U3_2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (KR2b : forall a, 0 <= a < 2 ^ 64 -> ~ Zw2 a ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms1) a = aview SEGS (w_H (c_W cx)) (ms_mem ms0) a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ _ HFr) end.
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha;
    rewrite ?U60, ?U44, ?U62, ?U3_2, ?UG2n, ?UG8n in Ha; unfold Zw2; clear - Ha HGLEN; lia |]).
  destruct Hin. }
clear HF HFr.
(* 0x808f4 beqz s3: an empty input (size 0) skips the first byte. *)
psrr_branch_tok RUNX BR HS SHOK2 hBspan0.
{ (* size = 0: 0x8091c s6 := 0, slot 32 := 0, then g_file := the input pointer, g_file_len := 0, malloc(0) *)
  rewrite branch_eq_U, (U_atom _ 11%nat (c_n cx) E3_11), (U_lit _ 0) in Hc by lia. apply Z.eqb_eq in Hc.
  assert (Epl : c_pl cx = []) by (unfold c_n in Hc; destruct (c_pl cx); [reflexivity | cbn in Hc; lia]).
  assert (EnF : p_nF cx = 0) by (unfold p_nF, p_F; rewrite Epl; reflexivity).
  assert (Esrc : p_src cx = c_p cx) by (unfold p_src; rewrite Epl; reflexivity).
  assert (Ed : p_d cx = 0) by (unfold p_d; rewrite Epl; reflexivity).
  paj_run_tok RUNX HS HJg2 SHOK2 hBspan0.
{ apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG8, ?UG8n in Ha. apply IG4. lia. }
    apply awr_ok_x_cons_g.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?UG2, ?UG2n in Ha. apply IG2. lia. }
    apply awr_ok_x_of0.
    lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 62%nat (pSH cx fpos)); [reflexivity | exact U62 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
      split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
      change (shadow_addr (frame_addr (c_ly cx) PE_CID fpos)) with (pSH cx fpos).
      change (fs_frame_bytes PE_CID / 8) with 16. lia. }
    apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 44%nat (pF cx fpos)); [reflexivity | exact U44 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists PE_CID, fpos.
      split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      change (frame_addr (c_ly cx) PE_CID fpos) with (pF cx fpos). change (fs_frame_bytes PE_CID) with 128. lia. }
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite U60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
    apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
      [reflexivity | rewrite U3_2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
    apply awr_ok_nil. }
  assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw2 a ->
    aview SEGS (w_H (c_W cx)) (ms_mem ms2) a = aview SEGS (w_H (c_W cx)) (ms_mem ms1) a).
  { lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ _ HFr) end.
    intros bb wlo whi a Hin Ha. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha;
      rewrite ?U60, ?U44, ?U62, ?U3_2, ?UG2n, ?UG8n in Ha; unfold Zw2; clear - Ha HGLEN; lia |]).
    destruct Hin. }
  clear HF HFr.
  
  pmkst HS. rewrite (pal_malloc B TL).
  repeat rewrite wvb_collapse in HJg2.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
  prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
  prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  pe_sregion HS 0%nat HRg4. pe_sregion HS 1%nat HRg2. pe_sregion HS 2%nat HRsh. pe_sregion HS 3%nat HRf.
  pe_sregion HS 4%nat HRs1. pe_sregion HS 5%nat HRst.
  apply (pe_E_malloc POST HK1 cx fpos 0 0 (c_ly cx) S2 (c_W cx) ms2 _ HB HJg2 Hfrs2).
  - rewrite ES2. apply (mo_le_set_fs_r MT MFSL). apply (mo_le_refl MT MTL).
  - lia.
  - lia.
  - rewrite Eab. apply Permutation_refl.
  - rewrite (proj1 (wvb_fds_fs _ _ _)). exact Efd2.
  - rewrite (proj2 (wvb_fds_fs _ _ _)). exact Efs2.
  - exact Q1.
  - rewrite Q2, E60. reflexivity.
  - rewrite Q3. exact (EE3 3%nat 3%bv eq_refl).
  - rewrite Q4. exact (EE3 4%nat 4%bv eq_refl).
  - rewrite Q8, E3_2. reflexivity.
  - rewrite Q9, E60. reflexivity.
  - rewrite Q10, EnF. reflexivity.
  - rewrite Q18. exact EG2.
  - rewrite Q20, E3_44. reflexivity.
  - rewrite Q21, Esrc, (EE3 10%nat 10%bv eq_refl). exact H10.
  - rewrite Q22, EnF. reflexivity.
  - rewrite Q23, E3_44. reflexivity.
  - rewrite Q25, E62. reflexivity.
  - rewrite Q27, E3_32, SB_SHADOW_OFF. reflexivity.
  - (* psaved: the stack region's 13 saves *)
    destruct (pe_saved_of E3v (w_H (c_W cx)) (ms_mem ms2) (spZ (c_regs cx)) (c_regs cx) _ _ _ _ _ HRst U3_2 EE3
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)) as [PS1 PS2].
    split; [exact PS1 | exact PS2].
  - (* pheader: the frame region's header words and flag pointer *)
    split; [|split; [|split]].
    + rewrite <- (Z.add_0_r (pF cx fpos)).
      exact (pe_word_at E3v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 0 (SLit 1102416563) PE_MAGIC HRf U44
        ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(unfold PE_MAGIC; lia)).
    + exact (pe_word_at E3v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 8 (SOff (A_OBJ 5) 0) (VAL (A_OBJ 5)) HRf U44
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        (pa_val_range (A_OBJ 5))).
    + exact (pe_word_at E3v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 16 (SOff (A_OBJ 6) 0) (VAL (A_OBJ 6)) HRf U44
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        (pa_val_range (A_OBJ 6))).
    + exact (pe_word_at E3v _ _ 44%nat (pF cx fpos) _ _ _ _ _ PE_FLAGPTR (SOff 61 0) (pFL cx fpos) HRf U44
        ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(lia)).
  - (* pshadow: the 16 shadow bytes PSH_entry *)
    exact (pe_shadow_bytes E3v _ _ 62%nat (pSH cx fpos) _ _ _ _ _ PSH_entry HRsh U62 ltac:(vm_compute; reflexivity)).
  - (* the input: empty *)
    rewrite Epl. intros j Hj. cbn in Hj. lia.
  - unfold pslot. exact (pe_word_at E3v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_D (SLit 0) (p_d cx) HRs1 U60
      ltac:(vm_compute; reflexivity) ltac:(rewrite Ed; reflexivity) ltac:(rewrite Ed; lia)).
  - unfold pslot. exact (pe_word_at E3v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_GLEN (SOff (A_HI 8) 0) (VAL (A_HI 8)) HRs1 U60
      ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      (pa_val_range (A_HI 8))).
  - unfold pslot. exact (pe_word_at E3v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_F0 (SOff 44 0) (pF cx fpos) HRs1 U60
      ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E3_44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(lia)).
  - (* p_glob: g_file = the input pointer, g_file_len = 0 *)
    unfold p_glob, pval. split.
    + apply (val_mem_of_rdword SEGS (w_H (c_W cx)) (ms_mem ms2)). rewrite <- (Z.add_0_r (VAL (A_OBJ 2))).
      exact (pe_word_at E3v _ _ (A_OBJ 2) (VAL (A_OBJ 2)) _ _ _ _ _ 0 (SOff 10 0) (p_src cx) HRg2 UG2
        ltac:(vm_compute; reflexivity)
        ltac:(cbn [sv_denot]; rewrite Esrc, (EE3 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10)
        ltac:(rewrite Esrc; destruct Hpn as [[_ Hpe] | [Hn _]]; [rewrite Hpe; unfold A_EMPTY; lia | lia])).
    + apply (val_mem_of_rdword SEGS (w_H (c_W cx)) (ms_mem ms2)). rewrite <- HGLEN.
      exact (pe_word_at E3v _ _ (A_HI 8) (VAL (A_HI 8)) _ _ _ _ _ PE_GLEN_LO (SLit 0) (p_nF cx) HRg4 UG8
        ltac:(vm_compute; reflexivity) ltac:(rewrite EnF; reflexivity) ltac:(rewrite EnF; lia)).
  - (* the stream environment: kept by every run (it is image, outside pe_G, the frame, its shadow and the stack) and
       by __asan_stack_malloc_1 (image, not an allocator static, not errno) *)
    apply (asource_none_frame_segs SEGS KS (rdW (c_W cx) (c_mem cx))); [|exact Hnone].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hns & Her). pose proof (pa_img_range a Hi) as Har.
    unfold pcap_img_end, YImgTop.IMG_TOP in Har.
    assert (HnG : ~ inG pe_G a) by (intros HG'; exact (HGENV a HG' Ha)).
    assert (HnZ : ~ Zw2 a).
    { unfold Zw2. intros Hw. apply HnG.
      destruct Hw as [Hw | [Hw | Hw]]; [apply IG4; exact Hw | apply IG2; exact Hw|].
      exfalso. clear - Hw Har HFo HSHr Hsp1 Hsp_lo C1. unfold SB in HSHr. lia. }
    pose proof HK as (_ & _ & K3 & _).
    rewrite (KR3 a ltac:(lia) HnZ), (KR2b a ltac:(lia) HnZ), (KR2 a ltac:(lia) HnZ), (K3 a Hi Hns Her).
    apply KR1; [lia|]. clear - Har Hsp_lo C1. lia.
}
(* size > 0: the input is one of the caller's blocks (pe_base); its first byte is the configuration byte d. *)
rewrite branch_eq_U, (U_atom _ 11%nat (c_n cx) E3_11), (U_lit _ 0) in Hc by lia. apply Z.eqb_neq in Hc.
destruct Hpn as [[Hn0 _] | [Hnpos Hinb]]; [lia|].
assert (Hpl : exists d0 F0, c_pl cx = d0 :: F0)
  by (unfold c_n in Hnpos; destruct (c_pl cx) as [|d0 F0]; [cbn in Hnpos; lia | exists d0, F0; reflexivity]).
destruct Hpl as (d0 & F0 & Epl).
assert (EnF : p_nF cx = c_n cx - 1) by (unfold p_nF, p_F, c_n; rewrite Epl; cbn [tl length]; lia).
assert (Esrc : p_src cx = c_p cx + 1) by (unfold p_src; rewrite Epl; reflexivity).
assert (Ed : p_d cx = bv_unsigned d0) by (unfold p_d; rewrite Epl; reflexivity).
pose proof (bv_unsigned_in_range 8 d0) as Hd0. change (bv_modulus 8) with 256 in Hd0.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinb) as (Hp16 & Hp4096 & Hpceil & Hpapp & _ & _ & _).
pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hreqn].
assert (Hinb2 : In (c_p cx, c_n cx) (ablocks B (c_ly cx) S2)) by (rewrite Eab; exact Hinb).
assert (Hfin2 : In (PE_CID, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hinb2 Hfin2) as DbF.
unfold zdisjoint in DbF. cbn [fst snd] in DbF. change (frame_addr (c_ly cx) PE_CID fpos) with (pF cx fpos) in DbF.
change (fs_frame_bytes PE_CID) with 128 in DbF.
(* the input block meets no window of the walk: it is app memory below the allocator's ceiling, not image, apart
   from the frame *)
assert (HbZ : forall i, 0 <= i < req_size (c_n cx) -> ~ Zw2 (c_p cx + i)).
{ intros i Hi Hw. pose proof (blk_img SEGS B LAWS _ _ _ _ _ _ _ (c_p cx + i) HAR Hinb ltac:(lia)) as Hni.
  unfold Zw2 in Hw. destruct Hw as [Hw | [Hw | Hw]].
  - apply Hni. exact (proj1 (HG _ (IG4 _ Hw))).
  - apply Hni. exact (proj1 (HG _ (IG2 _ Hw))).
  - clear - Hw Hi Hpapp DbF HSHr Hsp1 Hsp_lo Hpceil C1 C3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
    lia. }
assert (KIN : forall i, 0 <= i < req_size (c_n cx) ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms1) (c_p cx + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).
{ intros i Hi. pose proof HK as (_ & K2 & _).
  rewrite (KR2b (c_p cx + i) ltac:(lia) (HbZ i Hi)), (KR2 (c_p cx + i) ltac:(lia) (HbZ i Hi)),
    (K2 (c_p cx) (c_n cx) i Hinb Hi (fun H => H)).
  apply KR1; lia. }
assert (HIN0 : val_mem SEGS (rdW (c_W cx) (ms_mem ms1)) (c_p cx + 0) 1 (bv_unsigned d0)).
{ destruct (HPL 0%nat ltac:(rewrite Epl; cbn; lia)) as [Hv _]. rewrite Epl in Hv. cbn [map nth Z.of_nat] in Hv.
  eapply vm_frame_segs; [|exact Hv]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  replace x with (c_p cx + 0) by lia. apply KIN. lia. }
(* the frame and its shadow are not written again: read-only regions for the run with shadow tokens *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (pe_ro 62 (pe_ro 44 (ss_mem ssx))) in
  pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(pe_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
pe_norm_pi HS.
(* the configuration byte d as atom 63 *)
pose proof (st_ok_pi_havoc_hi 63 E3v _ _ [Z_to_bv 64 (bv_unsigned d0)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E3v 63 [Z_to_bv 64 (bv_unsigned d0)]) as E4v eqn:HE4 in HS.
assert (OLD4 : forall nn, (nn < 63)%nat -> ew E4v nn = ew E3v nn)
  by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
assert (E63 : ew E4v 63 = Z_to_bv 64 (bv_unsigned d0))
  by (rewrite HE4; exact (ew_havoc_new E3v 63 [Z_to_bv 64 (bv_unsigned d0)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEIm : img_env VAL A_LIM E4v) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
clear HE4.
assert (E4_10 : ew E4v 10 = Z_to_bv 64 (c_p cx)) by (rewrite OLD4 by lia; rewrite (EE3 10%nat 10%bv eq_refl); exact H10).
assert (U4_10 : bv_unsigned (ew E4v 10) = c_p cx) by (rewrite E4_10; apply unsigned_lit_small; lia).
assert (E4_32 : ew E4v 32 = Z_to_bv 64 SB) by (rewrite OLD4 by lia; exact E3_32).
assert (E4_11 : ew E4v 11 = Z_to_bv 64 (c_n cx)) by (rewrite OLD4 by lia; exact E3_11).
assert (E4_2 : ew E4v 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD4 by lia; exact E3_2).
assert (E4_44 : ew E4v 44 = Z_to_bv 64 (pF cx fpos)) by (rewrite OLD4 by lia; exact E3_44).
assert (E4_60 : ew E4v 60 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD4 by lia; exact E60).
assert (E4_61 : ew E4v 61 = Z_to_bv 64 (pFL cx fpos)) by (rewrite OLD4 by lia; exact E61).
assert (E4_62 : ew E4v 62 = Z_to_bv 64 (pSH cx fpos)) by (rewrite OLD4 by lia; exact E62).
assert (U4_60 : bv_unsigned (ew E4v 60) = c_sp1 cx) by (rewrite OLD4 by lia; exact U60).
assert (U4_44 : bv_unsigned (ew E4v 44) = pF cx fpos) by (rewrite OLD4 by lia; exact U44).
assert (U4_62 : bv_unsigned (ew E4v 62) = pSH cx fpos) by (rewrite OLD4 by lia; exact U62).
assert (U4_2 : bv_unsigned (ew E4v 2) = spZ (c_regs cx)) by (rewrite OLD4 by lia; exact U3_2).
assert (EE4 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E4v nn = getr (c_regs cx) r).
{ intros nn r Hn. pose proof (bv_unsigned_in_range 5 r) as Hb5. change (bv_modulus 5) with 32 in Hb5.
  rewrite OLD4 by lia. exact (EE3 nn r Hn). }
assert (EG2m : ew E4v (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (apply (img_env_atomP E4v (A_OBJ 2) HEIm); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG5m : ew E4v (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5)))
  by (apply (img_env_atomP E4v (A_OBJ 5) HEIm); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG6m : ew E4v (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
  by (apply (img_env_atomP E4v (A_OBJ 6) HEIm); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG8m : ew E4v (A_HI 8) = Z_to_bv 64 (VAL (A_HI 8)))
  by (apply (img_env_atomP E4v (A_HI 8) HEIm); unfold A_HI, A_TEXT, A_LIM; lia).
assert (UG2m : bv_unsigned (ew E4v (A_OBJ 2)) = VAL (A_OBJ 2)) by (rewrite EG2m; apply unsigned_lit_small; apply pa_val_range).
assert (UG8m : bv_unsigned (ew E4v (A_HI 8)) = VAL (A_HI 8)) by (rewrite EG8m; apply unsigned_lit_small; apply pa_val_range).
pose proof UG2m as UG2mn. pose proof UG8m as UG8mn.
lazymatch type of UG2mn with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG2mn end.
lazymatch type of UG8mn with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG8mn end.
pe_add_fact HS 10%nat (mkAF 4096 (2 ^ 47 - 16) 4)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U4_10; change (2 ^ 4) with 16; repeat split; lia).
pe_add_fact HS 63%nat (mkAF 0 255 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E63, unsigned_lit_small by lia; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
        repeat split; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 63 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U4_10; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
        apply Forall_cons; [|apply Forall_nil];
        apply (chunk_ok_val SEGS _ _ (c_p cx) 0 1 (SOff 63 0) (bv_unsigned d0));
        [cbn [sv_denot]; rewrite E63, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HIN0])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite ?U4_10, ?U4_60, ?U4_44, ?U4_62, ?U4_2, ?UG2mn, ?UG8mn;
        pose proof (HbZ 0 ltac:(lia)) as Hb0; unfold Zw2 in Hb0;
        clear - Hb0 HGLEN Hpapp Hpceil Hsp1 Hsp_lo C1; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; pe_norm_pi HS.
(* the input's first byte is addressable (the caller's block, AR's shadow law): the shadow check 0x808f8..0x80904
   and its slow block 0x81348 / 0x8134c are decided by this token, so the report call 0x81354 is never reached *)
assert (HRA : range_addressable (aview SEGS (w_H (c_W cx)) (ms_mem ms1)) SHADOW_OFF (c_p cx) 1)
  by (exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ (c_p cx) (c_n cx) (c_p cx) 1
       (ajournal_gx_AR (SK := SK) SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJg2) Hinb2 ltac:(lia) ltac:(lia))).
assert (SHOK3 : sh_ok SEGS (SOff 32 0) [mkSHE 10 0 1] E4v (rdW (c_W cx) (ms_mem ms1))).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E4v 32 SB E4_32) by (unfold SB; lia). rewrite (U_atom E4v 10 (c_p cx) E4_10) by lia.
  split.
  - rewrite Z.add_0_r, Z.sub_0_r, <- (aview_rd_of SEGS). rewrite SB_SHADOW_OFF. exact HRA.
  - intros a Ha. cbn in Ha. clear - Ha Hpapp Hreqn Hnpos C1 C3.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia. }
(* ---- R3 (size > 0): the shadow check of the first byte, d := it (slot 32), s5 := input + 1, s6 := size - 1,
   g_file := input + 1, g_file_len := size - 1, up to malloc (0x80940) ---- *)
paj_run_tok RUNX HS HJg2 SHOK3 (SB, SB + 2 ^ 44 - 1).
{ apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite ?UG8m, ?UG8mn in Ha. apply IG4. lia. }
  apply awr_ok_x_cons_g.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite ?UG2m, ?UG2mn in Ha. apply IG2. lia. }
  apply awr_ok_x_of0.
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?spx ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk spx fpp b0 bc lyy own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (c_sp1 cx - spZ (c_regs cx)));
    [reflexivity | rewrite U4_60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite U4_2; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil. }
(* the run's two shadow-token atoms (512, 513) leave every atom below them as it was *)
lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as E5v eqn:HE5 in * end.
assert (OLD5 : forall nn, (nn < 512)%nat -> ew E5v nn = ew E4v nn)
  by (intros nn Hnn; rewrite HE5; rewrite !ew_ewset_other by lia; reflexivity).
clear HE5.
assert (E5_10 : ew E5v 10 = Z_to_bv 64 (c_p cx)) by (rewrite OLD5 by lia; exact E4_10).
assert (E5_11 : ew E5v 11 = Z_to_bv 64 (c_n cx)) by (rewrite OLD5 by lia; exact E4_11).
assert (E5_2 : ew E5v 2 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD5 by lia; exact E4_2).
assert (E5_32 : ew E5v 32 = Z_to_bv 64 SB) by (rewrite OLD5 by lia; exact E4_32).
assert (E5_44 : ew E5v 44 = Z_to_bv 64 (pF cx fpos)) by (rewrite OLD5 by lia; exact E4_44).
assert (E5_60 : ew E5v 60 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD5 by lia; exact E4_60).
assert (E5_61 : ew E5v 61 = Z_to_bv 64 (pFL cx fpos)) by (rewrite OLD5 by lia; exact E4_61).
assert (E5_62 : ew E5v 62 = Z_to_bv 64 (pSH cx fpos)) by (rewrite OLD5 by lia; exact E4_62).
assert (E5_63 : ew E5v 63 = Z_to_bv 64 (bv_unsigned d0)) by (rewrite OLD5 by lia; exact E63).
assert (U5_10 : bv_unsigned (ew E5v 10) = c_p cx) by (rewrite OLD5 by lia; exact U4_10).
assert (U5_60 : bv_unsigned (ew E5v 60) = c_sp1 cx) by (rewrite OLD5 by lia; exact U4_60).
assert (U5_44 : bv_unsigned (ew E5v 44) = pF cx fpos) by (rewrite OLD5 by lia; exact U4_44).
assert (U5_62 : bv_unsigned (ew E5v 62) = pSH cx fpos) by (rewrite OLD5 by lia; exact U4_62).
assert (U5_2 : bv_unsigned (ew E5v 2) = spZ (c_regs cx)) by (rewrite OLD5 by lia; exact U4_2).
assert (EE5 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E5v nn = getr (c_regs cx) r).
{ intros nn r Hn. pose proof (bv_unsigned_in_range 5 r) as Hb5. change (bv_modulus 5) with 32 in Hb5.
  rewrite OLD5 by lia. exact (EE4 nn r Hn). }
assert (EG2v : ew E5v (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)))
  by (rewrite OLD5 by (unfold A_OBJ, A_TEXT; lia); exact EG2m).
assert (EG5v : ew E5v (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5)))
  by (rewrite OLD5 by (unfold A_OBJ, A_TEXT; lia); exact EG5m).
assert (EG6v : ew E5v (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
  by (rewrite OLD5 by (unfold A_OBJ, A_TEXT; lia); exact EG6m).
assert (EG8v : ew E5v (A_HI 8) = Z_to_bv 64 (VAL (A_HI 8)))
  by (rewrite OLD5 by (unfold A_HI, A_TEXT; lia); exact EG8m).
assert (UG2v : bv_unsigned (ew E5v (A_OBJ 2)) = VAL (A_OBJ 2)) by (rewrite EG2v; apply unsigned_lit_small; apply pa_val_range).
assert (UG8v : bv_unsigned (ew E5v (A_HI 8)) = VAL (A_HI 8)) by (rewrite EG8v; apply unsigned_lit_small; apply pa_val_range).
pose proof UG2v as UG2vn. pose proof UG8v as UG8vn.
lazymatch type of UG2vn with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG2vn end.
lazymatch type of UG8vn with bv_unsigned (ew ?Ex ?x) = _ => let v := eval vm_compute in x in change (ew Ex x) with (ew Ex v) in UG8vn end.
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ Zw2 a ->
  aview SEGS (w_H (c_W cx)) (ms_mem ms2) a = aview SEGS (w_H (c_W cx)) (ms_mem ms1) a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H (c_W cx)) _ _ _ HFr) end.
  intros bb wlo whi a Hin Ha. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha;
    rewrite ?U4_10, ?U4_60, ?U4_44, ?U4_62, ?U4_2, ?UG2mn, ?UG8mn in Ha; unfold Zw2; clear - Ha HGLEN; lia |]).
  destruct Hin. }
clear HF HFr.
pmkst HS. rewrite (pal_malloc B TL).
repeat rewrite wvb_collapse in HJg2.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
pe_sregion HS 1%nat HRg4. pe_sregion HS 2%nat HRg2. pe_sregion HS 3%nat HRsh. pe_sregion HS 4%nat HRf.
pe_sregion HS 5%nat HRs1. pe_sregion HS 6%nat HRst.
apply (pe_E_malloc POST HK1 cx fpos 0 0 (c_ly cx) S2 (c_W cx) ms2 _ HB HJg2 Hfrs2).
- rewrite ES2. apply (mo_le_set_fs_r MT MFSL). apply (mo_le_refl MT MTL).
- lia.
- lia.
- rewrite Eab. apply Permutation_refl.
- rewrite (proj1 (wvb_fds_fs _ _ _)). exact Efd2.
- rewrite (proj2 (wvb_fds_fs _ _ _)). exact Efs2.
- exact Q1.
- rewrite Q2, E5_60. reflexivity.
- rewrite Q3. exact (EE5 3%nat 3%bv eq_refl).
- rewrite Q4. exact (EE5 4%nat 4%bv eq_refl).
- rewrite Q8, E5_2. reflexivity.
- rewrite Q9, E5_60. reflexivity.
- rewrite Q10, E5_11, unsigned_lit_small by lia. rewrite EnF. reflexivity.
- rewrite Q18. exact EG2v.
- rewrite Q20, E5_44. reflexivity.
- rewrite Q21, E5_10, unsigned_lit_small by lia. rewrite Esrc. reflexivity.
- rewrite Q22, E5_11, unsigned_lit_small by lia. rewrite EnF. reflexivity.
- rewrite Q23, E5_44. reflexivity.
- rewrite Q25, E5_62. reflexivity.
- rewrite Q27, E5_32, SB_SHADOW_OFF. reflexivity.
- (* psaved: the stack region's 13 saves *)
  destruct (pe_saved_of E5v (w_H (c_W cx)) (ms_mem ms2) (spZ (c_regs cx)) (c_regs cx) _ _ _ _ _ HRst U5_2 EE5
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity)) as [PS1 PS2].
  split; [exact PS1 | exact PS2].
- (* pheader *)
  split; [|split; [|split]].
  + rewrite <- (Z.add_0_r (pF cx fpos)).
    exact (pe_word_at E5v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 0 (SLit 1102416563) PE_MAGIC HRf U5_44
      ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(unfold PE_MAGIC; lia)).
  + exact (pe_word_at E5v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 8 (SOff (A_OBJ 5) 0) (VAL (A_OBJ 5)) HRf U5_44
      ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG5v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      (pa_val_range (A_OBJ 5))).
  + exact (pe_word_at E5v _ _ 44%nat (pF cx fpos) _ _ _ _ _ 16 (SOff (A_OBJ 6) 0) (VAL (A_OBJ 6)) HRf U5_44
      ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG6v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      (pa_val_range (A_OBJ 6))).
  + exact (pe_word_at E5v _ _ 44%nat (pF cx fpos) _ _ _ _ _ PE_FLAGPTR (SOff 61 0) (pFL cx fpos) HRf U5_44
      ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E5_61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(lia)).
- (* pshadow PSH_entry *)
  exact (pe_shadow_bytes E5v _ _ 62%nat (pSH cx fpos) _ _ _ _ _ PSH_entry HRsh U5_62 ltac:(vm_compute; reflexivity)).
- (* the input block: written by no run, kept by __asan_stack_malloc_1 (a block of the caller) *)
  apply (garr8_frame SEGS (rdW (c_W cx) (c_mem cx)) (rdW (c_W cx) (ms_mem ms2)) _ _ HPL).
  intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS).
  change (Z.of_nat (length (c_pl cx))) with (c_n cx) in Ha. replace a with (c_p cx + (a - c_p cx)) by lia.
  rewrite (KR3 (c_p cx + (a - c_p cx)) ltac:(lia) (HbZ (a - c_p cx) ltac:(lia))).
  apply KIN. lia.
- unfold pslot. exact (pe_word_at E5v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_D (SOff 63 0) (p_d cx) HRs1 U5_60
    ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E5_63, Z.add_0_r, Z_to_bv_bv_unsigned, Ed; reflexivity)
    ltac:(rewrite Ed; lia)).
- unfold pslot. exact (pe_word_at E5v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_GLEN (SOff (A_HI 8) 0) (VAL (A_HI 8)) HRs1 U5_60
    ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite EG8v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    (pa_val_range (A_HI 8))).
- unfold pslot. exact (pe_word_at E5v _ _ 60%nat (c_sp1 cx) _ _ _ _ _ PS_F0 (SOff 44 0) (pF cx fpos) HRs1 U5_60
    ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite E5_44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(lia)).
- (* p_glob: g_file = input + 1, g_file_len = size - 1 *)
  unfold p_glob, pval. split.
  + apply (val_mem_of_rdword SEGS (w_H (c_W cx)) (ms_mem ms2)). rewrite <- (Z.add_0_r (VAL (A_OBJ 2))).
    exact (pe_word_at E5v _ _ (A_OBJ 2) (VAL (A_OBJ 2)) _ _ _ _ _ 0 (SOff 10 1) (p_src cx) HRg2 UG2v
      ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite U5_10, Esrc; reflexivity)
      ltac:(rewrite Esrc; lia)).
  + apply (val_mem_of_rdword SEGS (w_H (c_W cx)) (ms_mem ms2)). rewrite <- HGLEN.
    exact (pe_word_at E5v _ _ (A_HI 8) (VAL (A_HI 8)) _ _ _ _ _ PE_GLEN_LO (SOff 11 (-1)) (p_nF cx) HRg4 UG8v
      ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot]; rewrite E5_11, unsigned_lit_small by lia; rewrite EnF; reflexivity)
      ltac:(rewrite EnF; lia)).
- (* the stream environment: as in the empty-input arm *)
  apply (asource_none_frame_segs SEGS KS (rdW (c_W cx) (c_mem cx))); [|exact Hnone].
  intros a Ha. apply (mbyte_of_aview SEGS).
  destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Hns & Her). pose proof (pa_img_range a Hi) as Har.
  unfold pcap_img_end, YImgTop.IMG_TOP in Har.
  assert (HnG : ~ inG pe_G a) by (intros HG'; exact (HGENV a HG' Ha)).
  assert (HnZ : ~ Zw2 a).
  { unfold Zw2. intros Hw. apply HnG.
    destruct Hw as [Hw | [Hw | Hw]]; [apply IG4; exact Hw | apply IG2; exact Hw|].
    exfalso. clear - Hw Har HFo HSHr Hsp1 Hsp_lo C1. unfold SB in HSHr. lia. }
  pose proof HK as (_ & _ & K3 & _).
  rewrite (KR3 a ltac:(lia) HnZ), (KR2b a ltac:(lia) HnZ), (KR2 a ltac:(lia) HnZ), (K3 a Hi Hns Her).
  apply KR1; [lia|]. clear - Har Hsp_lo C1. lia.
Qed.

End c.
End b.
End a.

(* The sink head is EXPLICIT on the exported statement (a Theorem Labs lane, 21:57Z), as in PcapHarnessA.v / PcapHarnessTail.v. *)
Arguments pe_E {fx rc} SK {PI}.

(* pe_E is PcapEntryTop.v's Section top hypothesis pe_E at PI := PI_pcap, KS := pcap_KS, POST := pe_post: its type
   there, `forall fx, PFROM fx (GIx (@GI_K1) fx) -> PFROM fx (GIx (@GI_leave) fx) -> @pe_start fx rc SK PIp B MT pcap_KS
   (POSTP fx)`, is `fun fx => @pe_E fx rc SK PI_pcap B MT pcap_KS <Section premises> (POSTP fx)`. *)
