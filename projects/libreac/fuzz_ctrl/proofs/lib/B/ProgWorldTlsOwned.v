(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldTlsOwned.v b2656d49146 (the blob this tree had at release c5e779efe8c) (a working branch 09cdc671625, read by git show): the same lemmas, helpers and proof.  What differs from A is the image only: A.AF0m -> lib.Reusable.YF0m (image B's record tables: Tfib_owned_static, TFIB_TSD = 0x5fd9f8, ts_tsd / ts_owned), A.AB1v -> lib.Reusable.YB1v, A.AsanRT -> B.AsanRT, A.Prog.X -> B.Prog.X, A.ProgWorld / A.ProgWorld_Fs -> B.ProgWorld / B.ProgWorld_Fs.  cell_static's vm_compute runs over image B's own Tfib_owned_static: on B every byte of the 13 image cells lies in a row (measured first; the TP - 8 .. TP + 16 cell spans the two rows (0x5dc648, 8) and (0x5dc650, 0x3c), YF0m.v:2979 / 2965). *)
(* lib/B/ProgWorldTlsOwned.v -- fuzz_ctrl image B (libreac v1.9.0, asan-ubsan): proof of the announced statement
   B.ProgWorld.fp_tls_owned_stmt (ProgWorld.v Section CtlBase3, item (iii)).
   rule 24: no function proved (a closed check over YF0m's Tfib_owned_static and AR's ownership laws).

   THE ROUTE.  fp_tls (RcAsanFP.v:19-25) at DT = RT_TP + 32, TS = ly_tsd, C = ly_C, T = ly_T, DB = ly_D, k = 0 names
   sixteen cells.
   - Thirteen are closed image addresses: TLS_INDEX, REAL_TLS_GET_ADDR, TP - 8 .. TP + 16, DT + 8 = TP + 40, TSD_KEY_INITED,
     TSD_KEY, TP - 88, GOT_CF, CF + 137, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF, and TS + 8 k = ly_tsd (AR's am_tsd with
     CtrlTSyms' ts_tsd: ly_tsd = TFIB_TSD = 0x5fd9f8).  cell_static, one closed boolean run by vm_compute, checks that
     every byte of each lies in a row of Tfib_owned_static (= as_owned_static B by ts_owned).  YG0q.own_static then
     gives aowned: the row is owned, and AR's am_static_img puts it in ly_img, where no client byte lies (YG0q.nc_static).
   - C + 152, T + 48 and DB + 24 lie in the core extents (ly_C, 256), (ly_T, kThreadObjSize), (ly_D, 4096); YG0q.own_core
     gives aowned (layout_ok keeps those extents apart from the primary space, the side stack and every secondary map,
     so no live chunk or frame meets them).

   Image B's cells and the Tfib_owned_static rows (start, len) they lie in (YF0m.v), TP = B.AsanRT.RT_TP = 0x5dc650:
     TLS_INDEX [0xa15d0, 0xa15e0) in (0xa15d0, 16); REAL_TLS_GET_ADDR [0xa2690, 0xa2698) in (0xa25e8, 0x2878);
     TP - 8 .. TP + 16 [0x5dc648, 0x5dc660) in (0x5dc648, 8) + (0x5dc650, 0x3c); TP + 40 [0x5dc678, 0x5dc680) in
     (0x5dc650, 0x3c); TSD_KEY_INITED [0xa8f20, 0xa8f21) and TSD_KEY [0xa8f24, 0xa8f28) in (0xa8f10, 0x522e00);
     TP - 88 [0x5dc5f8, 0x5dc600) in (0x5dc5f8, 8); TS = TFIB_TSD [0x5fd9f8, 0x5fda00) in (0x5fd9f8, 8); GOT_CF
     [0xa08e0, 0xa08e8) in (0xa08d0, 0x20); CF + 137 [0x13b271, 0x13b272) and VERBOSITY [0x139158, 0x13915c) in
     (0xa8f10, 0x522e00); GOT_VERBOSITY [0xa0940, 0xa0948) in (0xa0910, 0x38); DTLS_TPOFF [0xa15e0, 0xa15e8) in
     (0xa15e0, 8).  (For the reader: the proof names each constant, and cell_static computes the check.) *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YG0f YG0n YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YF0m B.AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorld_Fs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- 1. The closed check: every byte of a cell lies in a row of Tfib_owned_static. ---- *)

Definition byte_static (x : Z) : bool :=
  existsb (fun r => andb (Z.leb (fst r) x) (Z.ltb x (fst r + snd r))) lib.Reusable.YF0m.Tfib_owned_static.

Definition cell_static (lo hi : Z) : bool :=
  forallb (fun i => byte_static (lo + Z.of_nat i)) (seq 0 (Z.to_nat (hi - lo))).

Lemma byte_static_sound : forall x, byte_static x = true ->
  Exists (lib.Reusable.YG0n.in_zr x) lib.Reusable.YF0m.Tfib_owned_static.
Proof.
  intros x H. unfold byte_static in H. apply existsb_exists in H as (r & Hr & Hx).
  apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  apply Exists_exists. exists r. split; [exact Hr|]. unfold lib.Reusable.YG0n.in_zr. lia.
Qed.

Lemma cell_static_sound : forall lo hi a, cell_static lo hi = true -> lo <= a < hi ->
  Exists (lib.Reusable.YG0n.in_zr a) lib.Reusable.YF0m.Tfib_owned_static.
Proof.
  intros lo hi a H Ha. unfold cell_static in H. rewrite forallb_forall in H.
  assert (Hi : In (Z.to_nat (a - lo)) (seq 0 (Z.to_nat (hi - lo)))) by (apply in_seq; lia).
  specialize (H _ Hi). rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia.
  exact (byte_static_sound a H).
Qed.

(* ---- 2. fp_tls_owned. ---- *)

Section TlsOwned.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma fp_tls_owned : B.ProgWorld.fp_tls_owned_stmt B.
Proof.
  intros TS LAWS ly S W m md a HAR Hex.
  destruct HAR as (M & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ M) as LO.
  pose proof (lib.Reusable.YG0n.am_tsd _ _ _ _ M) as Htsd.
  rewrite (lib.Reusable.YF0m.ts_tsd B TS) in Htsd.
  assert (HT : In (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize) (lib.Reusable.YG0f.owned_extents ly)).
  { unfold lib.Reusable.YG0f.owned_extents. right; right; left. reflexivity. }
  assert (HC : In (lib.Reusable.YG0f.ly_C ly, 256) (lib.Reusable.YG0f.owned_extents ly)).
  { unfold lib.Reusable.YG0f.owned_extents. do 6 right. left. reflexivity. }
  assert (HD : In (lib.Reusable.YG0f.ly_D ly, 4096) (lib.Reusable.YG0f.owned_extents ly)).
  { unfold lib.Reusable.YG0f.owned_extents. do 7 right. left. reflexivity. }
  destruct (B.ProgWorld_Fs.pw_owned_range ly _ LO HT) as [RT0 RT1].
  destruct (B.ProgWorld_Fs.pw_owned_range ly _ LO HC) as [RC0 RC1].
  destruct (B.ProgWorld_Fs.pw_owned_range ly _ LO HD) as [RD0 RD1].
  cbn [fst snd] in RT0, RT1, RC0, RC1, RD0, RD1.
  unfold lib.Reusable.YG0f.kThreadObjSize in RT1.
  unfold B.Prog.RcAsanFP.fp_tls in Hex.
  rewrite (B.ProgWorld_Fs.pw_u64 (B.AsanRT.RT_TP + 32)) in Hex by (unfold B.AsanRT.RT_TP; lia).
  rewrite Htsd in Hex.
  rewrite (B.ProgWorld_Fs.pw_u64 lib.Reusable.YF0m.TFIB_TSD) in Hex by (unfold lib.Reusable.YF0m.TFIB_TSD; lia).
  rewrite (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_C ly)), (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_T ly)),
    (B.ProgWorld_Fs.pw_u64 (lib.Reusable.YG0f.ly_D ly)) in Hex by lia.
  apply Exists_exists in Hex as (r & Hr & Ha).
  cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
    cbn [fst snd] in Ha.
  (* the sixteen cells in fp_tls order: the image cells by the closed check, C / T / DB by the core extents *)
  1-8, 11-15:
    (eapply lib.Reusable.YG0q.own_static; [exact M|]; rewrite (lib.Reusable.YF0m.ts_owned B TS);
     refine (cell_static_sound _ _ a _ Ha); vm_compute; reflexivity).
  - eapply lib.Reusable.YG0q.own_core with (e := (lib.Reusable.YG0f.ly_C ly, 256)); [exact M | |].
    + unfold lib.Reusable.YG0n.core_extents. do 4 right. left. reflexivity.
    + cbn [fst snd]. lia.
  - eapply lib.Reusable.YG0q.own_core
      with (e := (lib.Reusable.YG0f.ly_T ly, lib.Reusable.YG0f.kThreadObjSize)); [exact M | |].
    + unfold lib.Reusable.YG0n.core_extents. right. left. reflexivity.
    + cbn [fst snd]. unfold lib.Reusable.YG0f.kThreadObjSize. lia.
  - eapply lib.Reusable.YG0q.own_core with (e := (lib.Reusable.YG0f.ly_D ly, 4096)); [exact M | |].
    + unfold lib.Reusable.YG0n.core_extents. do 5 right. left. reflexivity.
    + cbn [fst snd]. lia.
Qed.
End TlsOwned.

Print Assumptions fp_tls_owned.
