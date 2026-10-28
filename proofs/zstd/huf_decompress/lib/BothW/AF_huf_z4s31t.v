From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s3b.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_z4s31k.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma z4s31_c4mod : forall m A (c : word) (V : Z) (jp : list byte) (p s l : word),
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 V); CB 4 jp; C8 p; C8 s; C8 l] ->
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 (V mod 2^32)); CB 4 jp; C8 p; C8 s; C8 l].
Proof.
  intros m A c V jp p s l RW.
  assert (E : le4 (Z_to_bv 64 V) = le4 (Z_to_bv 64 (V mod 2^32))).
  { unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite !Z_to_le_bytes_mod by (cbn; lia). reflexivity. }
  unfold rw_cells, cells_at in *. destruct RW as [[WF BA] WR].
  split; [split|].
  - exact WF.
  - cbn [cells_bytes cbytes] in BA |- *. rewrite <- E. exact BA.
  - exact WR.
Qed.

Lemma z4s31_NB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y11 y12 y13 y14 y15 : word) (b' : Z), 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 z10 y11 (Z_to_bv 64 (DST + (q + bv_unsigned z10))) y12
              y13 y14 y15 x17 x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
              (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90e34) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13
           x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64)
           (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90d74) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90e34] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 2 (2^32); KZRange (Qe - q) 2 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: let R43 := fresh "R43" in kx_range (EVar 43) R43.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_LA : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b c tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= q + 1 -> Qe <= dcap ->
  0 <= b < 2^32 -> 0 <= c < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q = Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90ec8) fc None mm (seg_rom bsegs))) ->
  (q + 1 = Qe -> forall (i : Z) (y10 y12 : word), 0 <= i < 2^tl ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 (Z_to_bv 64 i) (Z_to_bv 64 (DST + q)) y12 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90cd0) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90cb4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp SP DST dcap DT q Qe b c tl mtl
    SPL BD1 MI RS HD HDE HDC HQ HQ1 HQE HB HC HTL HMT HDT HSP K0 K1.
  unfold AZ4_SB in *.
  destruct (Z.eq_dec q Qe) as [E|E].
  - kx_runFmd [0x90ec8] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 0 0;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -312) 8 (DST + Qe);
      KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K0; lia.
  - kx_runFmd [0x90cd0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 1 1;
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZRange b 0 (2^32 - 1); KZRange c 0 (2^64 - 1);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b; KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -312) 8 (DST + Qe);
      KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4word4.
    all: try z4brx.
    all: try z4br.
    all: kx_post_regs_keep.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r18 ?r12 ?r13 ?r14 ?r15 ?r17 ?r25 ?r16 ?r19 ?r21 ?r22 ?r20 ?r23 ?r24 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) _ _ _ _ _ _) =>
      rewrite <- (Z_to_bv_bv_unsigned r11); eapply (K1 ltac:(lia) (bv_unsigned r11) r10 r12) end.
    all: lazymatch goal with
         | |- evtF _ _ _ _ => z4post_ez
         | |- 0 <= bv_unsigned (edenot ?E (EAlu ALU_SRL ?x ?s)) < 2^?t => apply (z4_srl_ltt E x s t); [lia | z4uzm]
         end.
Qed.

Lemma z4s31_br_shi : forall E X K,
  bv_unsigned (edenot E K) = 2^61 -> bv_unsigned (edenot E X) < 2^61 ->
  branch_taken BC_EQ (edenot E (EAlu ALU_SRL (EAlu ALU_ADD X K) (ELit 62))) (edenot E (ELit 0)) = true.
Proof.
  intros E X K HK HX.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [HX0 _].
  cbn [edenot branch_taken] in *.
  rewrite bv_eqb_Z, u_srl64, u_add64, HK.
  change (bv_unsigned (Z_to_bv 64 62)) with 62. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (62 mod 64) with 62.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma z4s31_LB : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y13 : word), bv_unsigned y10 = DT + 4 + 4 * i -> 1 <= bv_unsigned y11 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 1)
              y13 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90d44) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 i) (Z_to_bv 64 (DST + q)) x13
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90cd0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x90d44] 200%nat [true; true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_EQ (edenot ?E (EAlu ALU_SRL (EAlu ALU_ADD ?X ?K) (ELit 62))) _ = true => apply (z4s31_br_shi E X K); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: lazymatch goal with |- evtF _ _ _ _ => idtac | |- ?g => idtac "dbg: side" g end.
  all: kx_post_regs_keep.
  all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (ev _ ?n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => let R := fresh "R" in kx_range (EVar n) R end.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_br_sx63 : forall E X, 64 <= bv_unsigned (edenot E X) < 2^32 ->
  branch_taken BC_LTU (edenot E (ELit 63)) (edenot E (EExt true 0 4 X)) = true.
Proof.
  intros E X HX. cbn [edenot branch_taken] in *.
  rewrite bv_ltu_Z. change (bv_unsigned (Z_to_bv 64 63)) with 63.
  destruct (Z_lt_le_dec (bv_unsigned (edenot E X)) (2^31)) as [HS|HS].
  - rewrite u_ext_sx0_small by (cbn; lia). apply Z.ltb_lt. lia.
  - rewrite u_ext_sx0_high by (cbn; lia). apply Z.ltb_lt. lia.
Qed.

Lemma z4s31_LC : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i len : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 1 <= len <= 2 -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z),
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (DST + q + 1)) y12
              y13 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90ec8) fc None mm' (seg_rom bsegs))) ->
  (forall (mm' : amem) (y12 y13 : word) (v : Z), 0 <= v < 128 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) (Z_to_bv 64 (DST + q)) y12
              y13 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90eac) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 1)
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90d44) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 i len
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HI HLN HQD HTL HMT HDT HSP HB HC HTE HT2 K K2.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z.eq_dec len 1) as [LN1 | LN2]; [| assert (LN2' : len = 2) by lia; destruct (Z_le_gt_dec b 63) as [B63 | B64]].
  3: kx_runFmd [0x90ec8] 200%nat [true]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 64 (2^32 - 1); KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  2: kx_runFmd [0x90ec8] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 63; KZRange len 2 2; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x90ec8] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange len 1 1; KZRange i 0 4095; KZRange (2^tl - 1 - i) 0 4095; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s31_br_sx63 E X); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: kx_post_regs_keep.
  2: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (_ + bv_unsigned (ev _ ?n))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => let R := fresh "R" in kx_range (EVar n) R end.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: first [eapply K | eapply K2].
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_LD : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 v : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 1 = Qe -> 0 <= v < 128 -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b < 2^32 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (y10 y11 y12 y13 : word) (b' : Z),
     rw_cells bsegs mm' (SP + -384) (Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT) ->
     rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b'); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (DST + q + 1)) y12
              y13 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90ec8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) (Z_to_bv 64 (DST + q)) x13
           x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90eac) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 p s l jp cbs ob SP DST dcap DT q Qe b c tl mtl A2 L2 A3 L3 v
    SPL BD1 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQE HV HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 1 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  destruct (Z_lt_le_dec v 64) as [V64 | V64].
  2: kx_runFmd [0x90ec8] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 64 127; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  1: kx_runFmd [0x90ec8] 200%nat (@nil bool)
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange Qe 1 (2^32); KZRange (Qe - q) 1 1; KZRange (dcap - q) 1 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 (2^32 - 1); KZRange v 0 63; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -144) 8 c; KZWord (SP + -136) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -144) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brt.
  all: try z4shd.
  all: try (lazymatch goal with |- branch_taken BC_LTU (edenot ?E (ELit 63)) (edenot ?E (EExt true 0 4 ?X)) = true => apply (z4s31_br_sx63 E X); z4uz end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | z4uz | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s31_BR1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90d74) fc None mm (seg_rom bsegs))) ->
  (Qe < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90cb4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90cb0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) Qe) as [C|C].
  - kx_runFmd [0x90d74; 0x90cb4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x90d74; 0x90cb4] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (q + 2 - Qe) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s31_BR2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 : word)
    (SP DST dcap DT q Qe tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (q + 2 <= Qe ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90d74) fc None mm (seg_rom bsegs))) ->
  (Qe < q + 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90cb4) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90e34) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 SP DST dcap DT q Qe tl mtl SPL MI RS HD HDE HDC HQ HQE HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec (q + 2) Qe) as [C|C].
  - kx_runFmd [0x90d74; 0x90cb4] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (Qe - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact (K1 C).
  - kx_runFmd [0x90d74; 0x90cb4] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange (q + 2 - Qe) 1 2;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    apply K2; lia.
Qed.

Lemma z4s31_TN : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q Qe b tl mtl : Z),
  rw_cells bsegs mm (SP + -384)
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap -> 0 <= b < 2^32 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (forall mm' : amem,
     rw_cells bsegs mm' (SP + -384)
     [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] ->
     rw_cells bsegs mm' (SP + -144) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00); C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 (Z_to_bv 64 0x20e00) x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x90cb0) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
             (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x90ca4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 c p s l jp SP DST dcap DT q Qe b tl mtl SPL BD1 MI RS HD HDE HDC HQ HQE HB HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x90cb0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange b 0 (2^32 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge ].
Qed.

Definition K31X (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> (pt = 0 \/ Qe - q < 2) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90cb0) fc None mm (seg_rom bsegs)).

Definition K31N (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 64 < b < 2^31 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90ca4) fc None mm (seg_rom bsegs)).

Definition K31L (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> Qe < q + 2 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90cb4) fc None mm (seg_rom bsegs)).

Definition C31Bat (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z) : Prop :=
  forall (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q -> q + 2 <= Qe -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90d74) fc None mm (seg_rom bsegs)).

Definition C31B (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall q : Z, C31Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.

Definition C31T (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q : Z) (b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + Qe + -2)) x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90cb0) fc None mm (seg_rom bsegs)).

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_NLs : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) (q : Z),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  (forall q', q < q' -> C31Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q') ->
  C31Bat RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KL IH.
  unfold C31Bat.
  intros b c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 FS Hq Hq2 Hb.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  unfold C31Bat in IH.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_NB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 x11 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ =>
           first [eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4] | idtac "dbg: ztab" ]
       end).
  all: try assumption.
  all: try lia.
  intros mm' z10 y11 y12 y13 y14 y15 b' Hz10 SPL' BD1' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD1'.
  apply z4s31_c4mod in BD1'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                 (BD4A c (Z_to_bv 64 (b' mod 2^32)) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  pose proof (Z.mod_pos_bound b' (2^32) ltac:(lia)) as HBM.
  eapply (z4s31_BR2 Q RNG mm' FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 z10 y11 y12 y13 y14 y15 (Z_to_bv 64 (DST + Qe)) x18 x19 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 (bv_unsigned sp) DST dcap DT (q + bv_unsigned z10) Qe tl mtl);
    [exact SPL' | exact MI' | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply (IH (q + bv_unsigned z10)); [lia | exact FS' | lia | lia | exact HBM].
  - intros Hc. eapply KL; [exact FS' | lia | lia | exact HBM].
Qed.

Lemma z4s31_NL : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31B RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL.
  unfold C31B. intros q.
  remember (Z.to_nat (Qe - q)) as n eqn:Hn. revert q Hn.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros q Hn.
  apply (z4s31_NLs Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 q C D6 O6 L1 OL HQe KL).
  intros q' Hq'.
  destruct (Z_le_gt_dec q' Qe) as [Hle | Hgt].
  - apply (IHn (Z.to_nat (Qe - q'))); [lia | reflexivity].
  - unfold C31Bat. intros. lia.
Qed.

Lemma z4s31_T : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  C31T RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL.
  pose proof (z4s31_NL Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL) as NL.
  unfold C31B, C31Bat in NL.
  unfold C31T.
  intros q b c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x10 x11 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 FS Hq Hb.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_BR1 Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 x11 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 (bv_unsigned sp) DST dcap DT q Qe tl mtl);
    [exact SPL | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | |].
  - intros Hc. eapply NL; [exact FS | lia | lia | exact Hb].
  - intros Hc. eapply KL; [exact FS | lia | lia | exact Hb].
Qed.

Lemma z4s31_KX : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL.
  pose proof (z4s31_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL) as T.
  unfold C31T in T.
  unfold K31X. intros.
  eapply T; [eassumption | lia | lia].
Qed.

Lemma z4s31_KN : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL.
  pose proof (z4s31_T Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KL) as T.
  unfold C31T in T.
  unfold K31N.
  intros q b c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x10 x13 x14 x15 x16 x24 x25 x27 x28 x29 x31 FS Hq Hb.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  eapply (z4s31_TN Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x9 x10 (Z_to_bv 64 b) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 c p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp (bv_unsigned sp) DST dcap DT q Qe b tl mtl);
    [exact SPL | exact B1 | exact MI | exact FRS | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia |].
  intros mm' SPL' BD1' MI' MU' WM'.
  destruct BUF as (ob & OB & OBL).
  assert (MU3 : munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + -144, bv_unsigned sp + -144 + 40);
                       (DST, DST + dcap)] mm mm').
  { eapply munch_weaken; [| exact MU']. intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia. }
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
                 (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5
                      (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
                 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 0x20e00) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS | exact MU3 | exact WM' | exact MI' |  | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - exists ob. split; [| exact OBL].
      eapply u8arr_transport; [exact OB | exact MU' | exact WM' |]. rewrite length_map. cbn [disjoint_from]. lia.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  eapply T; [exact FS' | lia | lia].
Qed.

End CANSEC1.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4s31_LSd : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  forall (q b v : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q -> q + 1 = Qe -> 0 <= v < 128 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 v) (Z_to_bv 64 64) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90eac) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b v c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS Hq HQ1 HV Hb.
  unfold K31S2 in KS.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_LD Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x1 x1 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap v).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y12 y13 b' SPL' BD1' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD1'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b') jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  eapply KS. exact FS'.
Qed.

Lemma z4s31_LSc : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  forall (q b i len : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 1 <= len <= 2 -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 len) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 1) x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90d44) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b i len c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS Hq HQ1 HI HLN Hb.
  unfold K31S2 in KS.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_LC Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x1 x1 x1 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i len).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  - intros mm' y10 y11 y12 y13 b' SPL' BD1' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD1'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
             (BD4A c (Z_to_bv 64 b') jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply KS. exact FS'.
  - intros mm' y12 y13 v HV SPL' BD1' MI' MU' WM' BUF'.
    rewrite Z_to_bv_bv_unsigned in BD1'.
    assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
             (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
             (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
    { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
                cells cbs pdt SBL SBH rstk mm mm' (-144));
        [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
        | | exact B3S | | exact B2S | | apply BD4A_size].
      - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
      - unfold SPD. exact SPL'.
      - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
      - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
      - unfold BD4A. exact BD1'. }
    eapply (z4s31_LSd Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b v c p jp w0 w4 w5 w7 w8 w11 mm' x1 x5 x7 x8 y12 y13 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS'); lia.
Qed.

Lemma z4s31_LSb : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  forall (q b i : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) (mm : amem)
         (x1 x5 x7 x8 x10 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q -> q + 1 = Qe -> 0 <= i < 2^tl -> 0 <= b < 2^32 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 i) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
        x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
      FR (Z_to_bv 64 0x90cd0) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b i c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS Hq HQ1 HI Hb.
  unfold K31S2 in KS.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_LB Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x1 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp cbs ob
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl DT (DTABLE_BYTES mtl) DST dcap i).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  intros mm' y10 y11 y13 HY10 HY11 SPL' BD1' MI' MU' WM' BUF'.
  rewrite Z_to_bv_bv_unsigned in BD1'.
  assert (FS' : Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)))).
  { eapply (z4sf_rebuild3 AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src
              cells cbs pdt SBL SBH rstk mm mm' (-144));
      [exact C | exact D1 | lia | lia | exact FS |  | exact WM' | exact MI' | exact BUF' | | apply SPD_size | | exact B4S
      | | exact B3S | | exact B2S | | apply BD4A_size].
    - replace (bv_unsigned sp + -144 + 40) with (bv_unsigned sp + -104) by lia. exact MU'.
    - unfold SPD. exact SPL'.
    - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]. rewrite B4S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]. rewrite B3S. cbn [disjoint_from]. lia.
    - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]. rewrite B2S. cbn [disjoint_from]. lia.
    - unfold BD4A. exact BD1'. }
  rewrite <- (Z_to_bv_bv_unsigned y10), HY10. rewrite <- (Z_to_bv_bv_unsigned y11).
  eapply (z4s31_LSc Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b i (bv_unsigned y11) c p jp w0 w4 w5 w7 w8 w11 mm' x1 x5 x7 x8 y13 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS'); lia.
Qed.

Lemma z4s31_LS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS.
  unfold K31L.
  intros q b c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS Hq Hq2 Hb.
  unfold K31S2 in KS.
  assert (D1 : 1 <= dcap) by lia.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof C as C0.
  destruct C0 as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB0 & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof FS as FS0.
  destruct FS0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  pose proof (z4_body_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm C D1 MU)
    as (LCB & UT & RT & UD & RD & DT8 & DT0 & DTB & RSDT & DST8 & DST0 & RSDST & AP1 & AP2 & AP3 & AP4 & FLD
        & HB1 & HB2 & HB3 & HB4 & HB5 & HB6 & HB7 & HB8).
  pose proof (bv_unsigned_in_range _ c) as CR. unfold bv_modulus in CR.
  unfold SPD in SPL. unfold BD4A in B1.
  pose proof AP1 as AQ1. unfold KXGoM.apart in AQ1.
  destruct BUF as (ob & OB & OBL).
  eapply (z4s31_LA Q RNG mm FR fc gp tp x1 x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
            w0 w1 w4 w5 w7 w8 w10 w11 p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8)) jp
            (bv_unsigned sp) DST dcap DT q Qe b (bv_unsigned c) tl mtl).
  all: try (lazymatch goal with
       | |- rw_cells _ _ _ (C8 (Z_to_bv 64 (bv_unsigned _)) :: _) => rewrite Z_to_bv_bv_unsigned; exact B1
       | |- ztab_fact _ _ _ _ _ _ => eapply z4_x2tab_fact_gen; [exact TOK | rewrite <- ECB; exact BDT4]
       end).
  all: try assumption.
  all: try lia.
  - intros E. eapply KS. exact FS.
  - intros E i y10 y12 HI.
    eapply (z4s31_LSb Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS q b i c p jp w0 w4 w5 w7 w8 w11 mm x1 x5 x7 x8 y10 y12 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 FS); lia.
Qed.

Lemma z4s31_KXS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31X RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS.
  exact (z4s31_KX Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe (z4s31_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS)).
Qed.

Lemma z4s31_KNS : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region) (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  6 <= dcap -> 6 <= O -> 1 <= Lk -> O + Lk <= zlen src -> 0 <= Qe <= dcap ->
  K31S2 RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 ->
  K31N RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cbs Q O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS.
  exact (z4s31_KN Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe (z4s31_LS Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk O Lk Qe w1 w10 x9 x18 x19 bd4 bd3 bd2 C D6 O6 L1 OL HQe KS)).
Qed.

End CANSEC1.
