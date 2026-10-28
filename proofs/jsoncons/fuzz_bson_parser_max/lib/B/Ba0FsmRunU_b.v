(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0TlsGetAddr_b Ba0FakeStackGC_b Ba0FakeStackGCC_b
  Ba0Fsm1Gen_b Ba0Fsm3Gen_b Ba0Fsm1Post_b Ba0Fsm3Post_b Ba0Fsm1Run_b Ba0Fsm3Run_b.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition fsm_colg (gcb : bool) (s top botth : Z) (flag rs : Z -> Z -> Z) (c i : Z) : Prop := gcb = true /\ (s <= top)%Z /\ gc_col s botth flag rs c i.
(* [comment removed for export] *)
Definition fsm_gbf (gcb : bool) (s top : Z) : Z := if (gcb && (top <? s)%Z)%bool then 1%Z else 0%Z.

(* [comment removed for export] *)
Definition fsm_fp_u (k fs pos ff : Z) (col : Z -> Z -> Prop) (a : Z) : Prop :=
  (fs + 8 * k <= a < fs + 8 * k + 8)%Z \/ a = (fs + 96)%Z \/ a = gc_fl fs k pos \/ (ff + 24 <= a < ff + 32)%Z \/ (ff + (2 ^ (6 + k) - 8) <= a < ff + (2 ^ (6 + k) - 8) + 8)%Z
  \/ (SB + ff / 8 <= a < SB + ff / 8 + 2 ^ (3 + k))%Z
  \/ (exists c i, gc_valid c i /\ col c i /\ (a = gc_fl fs c i \/ gc_insh fs c i a)).
Definition fsm_post_u (gb k : Z) (mem0 Mf : word -> option byte) (lo hi s fs h j pos ff : Z) (col : Z -> Z -> Prop) : Prop :=
  mem_grows mem0 Mf
  /\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> ~ fsm_fp_u k fs pos ff col (bv_unsigned x) -> Mf x = mem0 x)
  /\ rdn ASEGS Mf (Z_to_bv 64 (fs + 8 * k)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))
  /\ rdn ASEGS Mf (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb]
  /\ rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs k pos)) 1%nat = Some [Z_to_bv 8 1]
  /\ (forall c i, gc_valid c i -> col c i -> ~ (c = k /\ i = pos) -> rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 0])
  /\ rdn ASEGS Mf (Z_to_bv 64 (ff + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 s))
  /\ rdn ASEGS Mf (Z_to_bv 64 (ff + (2 ^ (6 + k) - 8))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (gc_fl fs k pos)))
  /\ (forall i, (0 <= i < 2 ^ (3 + k))%Z -> Mf (Z_to_bv 64 (SB + ff / 8 + i)) = Some (Z_to_bv 8 0)).

Definition fsm_run_u (k : Z) (entry : word) : Prop :=
  forall (fx : PropExec.FPState),
    forall (mem0 : word -> option byte),
    forall (rom : word -> option byte),
    forall (sp ra a0v : word),
    forall (s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z),
    (* [comment removed for export] *) (bv_unsigned sp = s) ->
    (* [comment removed for export] *) (ret_ok ra) ->
    (* [comment removed for export] *) ((0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) (store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true) ->
    (* [comment removed for export] *) ((96 <= tpv < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= md < 255)%Z) ->
    (* [comment removed for export] *) ((0 <= off < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= ent < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= key < 2 ^ 28)%Z) ->
    (* [comment removed for export] *) ((0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 < th /\ th + 64 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= F /\ F + 256 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= V /\ V + 4 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= verb < 3)%Z) ->
    (* [comment removed for export] *) ((0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z) ->
    (* [comment removed for export] *) ((0 < rec < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) (forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) -> tls_cells tpv 0x1382b8 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M') ->
    forall (fs : Z),
    (* [comment removed for export] *) ((0 < fs < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= tls_rp off ent /\ tls_rp off ent + 8 < 2 ^ 64)%Z /\ (tls_rp off ent + 8 <= s - 208 \/ s <= tls_rp off ent)%Z) ->
    (* [comment removed for export] *) (rdn ASEGS mem0 (Z_to_bv 64 (tls_rp off ent)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs))) ->
    forall (h j pos ff : Z),
    forall (top botth g40 g35 : Z),
    forall (flag rs : Z -> Z -> Z),
    forall (gcb : bool),
    (* [comment removed for export] *) ((0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z) ->
    (* [comment removed for export] *) ((fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z) ->
    (* [comment removed for export] *) ((gc_shz_hi fs <= s - 208 \/ s <= gc_shz_lo fs)%Z) ->
    (* [comment removed for export] *) ((0 <= h < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) ((0 <= j < 2 ^ (14 - k))%Z) ->
    (* [comment removed for export] *) (pos = ((h + j) mod 2 ^ (14 - k))%Z) ->
    (* [comment removed for export] *) (ff = gc_fr fs k pos) ->
    (* [comment removed for export] *) (rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 (if gcb then 1 else 0)]) ->
    (* [comment removed for export] *) (rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))) ->
    (* [comment removed for export] *) (rdn ASEGS mem0 (Z_to_bv 64 (fs + 8 * k)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h))) ->
    (* [comment removed for export] *) (forall c i, gc_valid c i -> rdn ASEGS mem0 (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z) ->
    (* [comment removed for export] *) (forall i, (0 <= i < j)%Z -> flag k ((h + i) mod 2 ^ (14 - k))%Z <> 0%Z /\ ~ fsm_colg gcb s top botth flag rs k ((h + i) mod 2 ^ (14 - k))%Z) ->
    (* [comment removed for export] *) (flag k pos = 0%Z \/ fsm_colg gcb s top botth flag rs k pos) ->
    (* [comment removed for export] *) (store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true) ->
    (* [comment removed for export] *) (rt_layout_globs mem0) ->
    (* [comment removed for export] *) (store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) (Z.to_nat (2 ^ (3 + k))) = true) ->
    (* [comment removed for export] *) (gcb = true -> (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= s)%Z) ->
    (* [comment removed for export] *) (gcb = true -> (th + 80 <= 2 ^ 64)%Z) ->
    (* [comment removed for export] *) (gcb = true -> forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) -> rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\ rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\ rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\ rdn ASEGS M' (0x1374b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\ rdn ASEGS M' (0x10380 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35))) ->
    (* [comment removed for export] *) (gcb = true -> forall M', (forall x : word, gc_outz (s - 208) s fs (bv_unsigned x) -> M' x = mem0 x) -> forall c i, gc_valid c i -> flag c i <> 0%Z -> rdn ASEGS M' (Z_to_bv 64 (gc_fr fs c i + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i))) /\ (0 <= rs c i < 2 ^ 64)%Z) ->
    (* [comment removed for export] *) (forall c i, gc_valid c i -> fsm_colg gcb s top botth flag rs c i -> (c <= 6)%Z) ->
    (* [comment removed for export] *) (forall c i, gc_valid c i -> fsm_colg gcb s top botth flag rs c i -> store_ok ASEGS mem0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true) ->
    forall regs : bvmap 5 word,
    getr regs 10 = a0v -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mf,
      msteps ASEGS (mkst regs entry mem0 rom) (mkst regs' ra Mf rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ fsm_post_u (fsm_gbf gcb s top) k mem0 Mf (s - 208) s s fs h j pos ff (fsm_colg gcb s top botth flag rs).

#[local] Ltac pw e := let v := eval vm_compute in e in change e with v.

Lemma fsm_run_u_1 : fsm_run_u 1 (0x5dda0 : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 2 ^ 20 + 128 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 1))%Z; lia).
  destruct (@fsm1_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.

Lemma fsm_run_u_3 : fsm_run_u 3 (0x5df30 : word).
Proof.
  unfold fsm_run_u. intros fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def Hff_def Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1.
  assert (HFF : ff = (fs + 4096 + 32768 + 3145728 + 512 * pos)%Z) by (rewrite Hff_def; unfold gc_fr; pw (2 ^ (6 + 3))%Z; lia).
  destruct (@fsm3_run_any fx mem0 rom sp ra a0v s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec Hs_def Hret Hs Hok Htp Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec HC0 fs Hfs0 Hr HRfs h j pos ff top botth g40 g35 flag rs gcb Hfs Happm Hshz Hh Hj Hpos_def HFF Hng Hssl Hhint HF0 Hprobe Hflag Hwfs HG Hshadow_ok Htop Hth80 HCG HRS Hcol6 Hshok regs H10 H4 H2 H1) as (r' & Mf & RUN & Q10 & Q2 & Q1 & KCS & POST).
  exists r', Mf. split; [exact RUN|]. split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [exact KCS|]. exact POST.
Qed.
