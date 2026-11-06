(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Record pcap_consts := mkPK {
  pk_next_pcap : Z;     (* [comment removed for export] *)
  pk_next_ng : Z;       (* [comment removed for export] *)
  pk_cleanup_sf : Z;    (* [comment removed for export] *)
  pk_cleanup_ng : Z;    (* [comment removed for export] *)
  pk_oneshot : Z;       (* [comment removed for export] *)
  pk_stats : Z          (* [comment removed for export] *)
}.
Definition PK : pcap_consts := mkPK 0x153f0 0x173f4 0x14190 0x17ae8 0x14694 0x14634.

(* [comment removed for export] *)
Definition PCAP_NEXT_EX_ENTRY : Z := 0x146bc.
Definition PCAP_OFFLINE_READ_ENTRY : Z := 0x144c8.
Definition PCAP_STATS_ENTRY : Z := 0x148a0.
Definition PCAP_CLOSE_ENTRY : Z := 0x14724.
Definition PCAP_FREECODE_ENTRY : Z := 0x14660.
Definition PCAP_OPEN_OFFLINE_ENTRY : Z := 0x144a4.
Definition PCAP_OPEN_OFFLINE_WTP_ENTRY : Z := 0x141d8.
Definition PCAP_FOPEN_OFFLINE_WTP_ENTRY : Z := 0x142d4.
Definition PCAP_OPEN_OFFLINE_COMMON_ENTRY : Z := 0x14760.
Definition PCAP_CHECK_HEADER_ENTRY : Z := 0x14f5c.
Definition PCAP_NG_CHECK_HEADER_ENTRY : Z := 0x1661c.
Definition PCAP_ADJUST_SNAPSHOT_ENTRY : Z := 0x144b0.
Definition LINKTYPE_TO_DLT_ENTRY : Z := 0x158cc.
Definition MAX_SNAPLEN_ENTRY : Z := 0x15908.
Definition PCAP_POST_PROCESS_ENTRY : Z := 0x15940.
Definition PCAP_STRERROR_ENTRY : Z := 0x147f4.
Definition PCAP_FMT_ERRMSG_ENTRY : Z := 0x148b4.
Definition READ_BYTES_ENTRY : Z := 0x16b48.
Definition READ_BLOCK_ENTRY : Z := 0x16c20.
Definition ADD_INTERFACE_ENTRY : Z := 0x16f44.

(* [comment removed for export] *)
Definition GOT_PCAP_ADDR : Z := 0x225d0.
Definition GOT_INSTALL_BPF : Z := 0x1496c.
Definition GOT_BREAKLOOP : Z := 0x148a8.

(* [comment removed for export] *)
Definition FILE_BLOCK : Z := 1264.    (* [comment removed for export] *)
Definition PCAP_HDR_OFF : Z := 520.   (* [comment removed for export] *)
Definition PCAP_ERRBUF_OFF : Z := 216.
Definition PCAP_PRIV_OFF : Z := 648.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eqz_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof using Type. pin_using tt. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma nez_true : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof using Type. pin_using tt. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
Lemma eqb_lits_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using Type. pin_using tt. intros x y Hx Hy Hne. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

(* [comment removed for export] *)
Lemma and7_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 8 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0%Z.
Proof using Type. pin_using tt.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Ha.
Qed.
Lemma and3_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 4 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0%Z.
Proof using Type. pin_using tt.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2)%Z with 4%Z. exact Ha.
Qed.
Lemma aligned16_8 : forall x k, (x mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((x + k) mod 8 = 0)%Z.
Proof using Type. pin_using tt.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 2) * 8)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rep.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  Definition b8 (z : Z) : byte := Z_to_bv 8 z.

  Definition is_ng (p : pcapT) : bool := match pc_priv p with PrivNg _ _ => true | PrivPcap _ => false end.
  Definition np_entry (p : pcapT) : Z := if is_ng p then pk_next_ng PK else pk_next_pcap PK.
  Definition cleanup_entry (p : pcapT) : Z := if is_ng p then pk_cleanup_ng PK else pk_cleanup_sf PK.
  (* [comment removed for export] *)
  Definition psize (p : pcapT) : Z := if is_ng p then PCAP_NG_SF_TOTAL else PCAP_SF_TOTAL.

  (* [comment removed for export] *)
  Definition hdr_cells (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

  (* [comment removed for export] *)
  Record pcap_junk := mkPJ {
    pj_read_op : word;      (* [comment removed for export] *)
    pj_fd : word;           (* [comment removed for export] *)
    pj_a : list byte;       (* [comment removed for export] *)
    pj_b : list byte;       (* [comment removed for export] *)
    pj_c : list byte;       (* [comment removed for export] *)
    pj_d : list byte;       (* [comment removed for export] *)
    pj_e : list byte;       (* [comment removed for export] *)
    pj_f : list byte;       (* [comment removed for export] *)
    pj_g : list byte;       (* [comment removed for export] *)
    pj_h : list byte;       (* [comment removed for export] *)
    pj_breakloop : word     (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pc_pre (p : pcapT) (P B : Z) (rf : cell) (j : pcap_junk) : list cell :=
    [ C8 (pj_read_op j);                         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (np_entry p));              (* [comment removed for export] *)
      C4 (pj_fd j);                              (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_bufsize p));            (* [comment removed for export] *)
      C8 (Z_to_bv 64 B);                         (* [comment removed for export] *)
      CB 12 (pj_a j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_break_loop p));         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF));       (* [comment removed for export] *)
      C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)));    (* [comment removed for export] *)
      CB 4 (pj_b j);                             (* [comment removed for export] *)
      rf;                                        (* [comment removed for export] *)
      CB 16 (pj_c j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_major p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_minor p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_snapshot p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype_ext p));       (* [comment removed for export] *)
      CB 12 (pj_d j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
      CB 28 (pj_e j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_tstamp_precision p));   (* [comment removed for export] *)
      CB 48 (pj_f j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0) ].                       (* [comment removed for export] *)
  Definition pc_ops (p : pcapT) (st os : cell) (j : pcap_junk) : list cell :=
    [ CB 72 (pj_h j);                            (* [comment removed for export] *)
      st;                                        (* [comment removed for export] *)
      C8 (pj_breakloop j);                       (* [comment removed for export] *)
      os;                                        (* [comment removed for export] *)
      C8 (Z_to_bv 64 (cleanup_entry p)) ].       (* [comment removed for export] *)
  Definition pcap_cells_gen (p : pcapT) (P B : Z) (rf st os : cell) (j : pcap_junk) : list cell :=
    pc_pre p P B rf j ++ [CB 304 (pj_g j)] (* [comment removed for export] *) ++ hdr_cells (pc_header p) (* [comment removed for export] *) ++ pc_ops p st os j.

  Definition pcap_cells (p : pcapT) (P B Af : Z) (j : pcap_junk) : list cell :=
    pcap_cells_gen p P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j.

  Remark pcap_cells_size : forall p P B Af j, cells_size (pcap_cells p P B Af j) = 648%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition lenswap_code (l : lenswap_t) : Z := match l with NOT_SWAPPED => 0 | SWAPPED => 1 | MAYBE_SWAPPED => 2 end.
  Definition sfscale_code (t : sf_scale_t) : Z := match t with SF_PASS_THROUGH => 0 | SF_SCALE_UP => 1 | SF_SCALE_DOWN => 2 end.
  Definition ngscale_code (t : ng_scale_t) : Z :=
    match t with NG_PASS_THROUGH => 0 | SCALE_UP_DEC => 1 | SCALE_DOWN_DEC => 2 | SCALE_UP_BIN => 3 | SCALE_DOWN_BIN => 4 end.
  Definition is_dec (t : ng_scale_t) : bool := match t with SCALE_UP_DEC | SCALE_DOWN_DEC => true | _ => false end.

  (* [comment removed for export] *)
  Definition sf_cells (s : pcap_sf) : list cell :=
    [C8 (Z_to_bv 64 (sf_hdrsize s)); C4 (Z_to_bv 64 (lenswap_code (sf_lengths_swapped s))); C4 (Z_to_bv 64 (sfscale_code (sf_scale_type s)))].
  (* [comment removed for export] *)
  Definition ng_cells (s : pcap_ng_sf) (I : Z) (pad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (ng_user_tsresol s)); C4 (Z_to_bv 64 (ng_max_blocksize s)); C4 (Z_to_bv 64 (ng_ifcount s));
     C4 (Z_to_bv 64 (ng_ifaces_size s)); CB 4 pad; C8 (Z_to_bv 64 I)].
  Definition priv_cells (p : pcapT) (I : Z) (pad : list byte) : list cell :=
    match pc_priv p with PrivPcap s => sf_cells s | PrivNg s _ => ng_cells s I pad end.

  (* [comment removed for export] *)
  Record if_junk := mkIJ { ij_p1 : list byte; ij_p2 : list byte; ij_sf : word }.
  Definition if_cells (i : ng_if) (j : if_junk) : list cell :=
    [C4 (Z_to_bv 64 (if_snaplen i)); CB 4 (ij_p1 j); C8 (Z_to_bv 64 (if_tsresol i)); C4 (Z_to_bv 64 (ngscale_code (if_scale_type i)));
     CB 4 (ij_p2 j); C8 (if is_dec (if_scale_type i) then Z_to_bv 64 (if_scale_factor i) else ij_sf j); C8 (Z_to_bv 64 (if_tsoffset i))].
  Fixpoint ifs_cells (ifs : list ng_if) (js : list if_junk) : list cell :=
    match ifs, js with
    | i :: ifs', j :: js' => if_cells i j ++ ifs_cells ifs' js'
    | _, _ => []
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition if_wf (i : ng_if) : Prop :=
    0 < if_tsresol i < 2^64 /\ (is_dec (if_scale_type i) = true -> 0 < if_scale_factor i < 2^64).

  Definition ifaces_ok (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0 /\ ng_ifaces s = [] /\ ng_ifcount s = 0 /\ ng_ifaces_size s = 0
    | PrivNg s (Some q) =>
        exists js tail, length js = length (ng_ifaces s)
          /\ rw_cells ssegs m I (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail])
          /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)) /\ ng_ifcount s <= ng_ifaces_size s /\ 1 <= ng_ifaces_size s < 2^26
          /\ Forall if_wf (ng_ifaces s)
    end.

  (* [comment removed for export] *)
  Definition pcap_blocks (p : pcapT) (P B I : Z) : list cblk :=
    (pc_self p, P, psize p) :: (pc_buffer p, B, pc_bufalloc p)
    :: match pc_priv p with
       | PrivNg s (Some q) => [(q, I, 40 * ng_ifaces_size s)]
       | _ => []
       end.

  (* [comment removed for export] *)
  Definition pcap_wf (p : pcapT) : Prop :=
    1 <= pc_snapshot p <= INT_MAX
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= pc_bufalloc p < 2^32
    /\ Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p
    /\ pc_break_loop p = 0 /\ pc_tstamp_precision p = 0
    /\ 0 <= pc_version_major p < 2^16 /\ 0 <= pc_version_minor p < 2^16
    /\ 0 <= pc_linktype p < 2^31 /\ -2^31 <= pc_linktype_ext p < 2^31
    /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32
    /\ match pc_priv p with
       | PrivPcap s => sf_hdrsize s = 16 \/ sf_hdrsize s = 24
       | PrivNg s _ => 0 < ng_user_tsresol s < 2^64 /\ 0 <= ng_max_blocksize s <= 2^30 /\ 0 <= ng_ifcount s < 2^32 /\ 0 <= ng_ifaces_size s < 2^32
       end
    /\ pc_bufsize p <= pc_bufalloc p.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PCAPRg (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells ssegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_ok p I m
    /\ pcap_wf p.

  (* [comment removed for export] *)
  Definition PCAPR (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  (* [comment removed for export] *)
  Definition pre_PCAPR (P : Z) (p : pcapT) (PB : list cblk) (m : mem) : Prop :=
    exists rf st os, length rf = 8%nat /\ length st = 8%nat /\ length os = 8%nat /\ PCAPRg P p PB (CB 8 rf) (CB 8 st) (CB 8 os) m.

  (* [comment removed for export] *)
  Definition ifaces_closable (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0
    | PrivNg s (Some q) => (exists junk, rw_cells ssegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.
  Definition PCAPRg_closable (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells ssegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_closable p I m
    /\ pcap_wf p.
  Definition PCAPR_closable (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg_closable P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIo (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) : Prop :=
       mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB)
    /\ 0x7fff80000000 <= usp0 R <= 2^47
    /\ CEILZ <= rc_lo R.                      (* [comment removed for export] *)

  Lemma GI_open : forall R s CL m, GI K R s CL m <-> exists FB, GIo R s CL FB m.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma GIo_close : forall R s CL FB m, GIo R s CL FB m -> GI K R s CL m.
  Proof using Type. pin_using tt. intros R s CL FB m G. exists FB. exact G. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition std_pre_o (sp tp : word) (R : rctx) (s : PS) (CL FB : list cblk) (lo budget : Z) (m : mem) : Prop :=
    GIo R s CL FB m /\ stk ssegs m lo (bv_unsigned sp) /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp
    /\ bv_unsigned sp <= rc_spmain R /\ mem_inv ssegs m /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0.

  Lemma std_pre_o_close : forall sp tp R s CL FB lo budget m,
    std_pre_o sp tp R s CL FB lo budget m -> std_pre K sp tp R s CL lo budget m.
  Proof using Type. pin_using tt.
    intros sp tp R s CL FB lo budget m (G & A & B & C & D & E & F & AL). unfold std_pre.
    split; [eapply GIo_close; exact G|]. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact AL].
  Qed.

  Lemma aln16_add : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a + k) mod 16 = 0.
  Proof using Type. pin_using tt. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma GIo_blocks : forall R s CL FB m, GIo R s CL FB m -> blocks_ok (utp R) (CL ++ FB).
  Proof using Type. pin_using tt. intros R s CL FB m G. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 G)))))))))))). Qed.

  Lemma GIo_tls : forall R s CL FB m, GIo R s CL FB m -> ps_tls s = utp R - 200 /\ tls_block_ok (utp R - 200).
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & T & _). auto. Qed.

  (* [comment removed for export] *)
  Lemma GIo_spw : forall R s CL FB m, GIo R s CL FB m -> 0x7fff80000000 <= usp0 R /\ CEILZ <= usp0 R - 8388608.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & C). unfold rc_lo in C. exact (conj (proj1 W) C). Qed.
  Lemma GIo_sp47 : forall R s CL FB m, GIo R s CL FB m -> usp0 R <= 2^47.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _). exact (proj2 W). Qed.
  Lemma GIo_ceil_lo : forall R s CL FB m, GIo R s CL FB m -> CEILZ <= rc_lo R.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C). exact C. Qed.

  Lemma GIo_pcap_tls : forall R s CL FB m, GIo R s CL FB m -> PCAP_TLS R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & PT & _). exact PT. Qed.

  Lemma GIo_core_tls : forall R s CL FB m, GIo R s CL FB m -> CORE_TLS R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & CT & _). exact CT. Qed.

  Lemma GIo_core_misc : forall R s CL FB m, GIo R s CL FB m -> CORE_MISC m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & CM & _). exact CM. Qed.

  Lemma GIo_core_libc : forall R s CL FB m, GIo R s CL FB m -> CORE_LIBC R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & CLI & _). exact CLI. Qed.

  (* [comment removed for export] *)
  Lemma GIo_got_pcap : forall R s CL FB m, GIo R s CL FB m ->
    rw_cells ssegs m GOT_PCAP_ADDR [C8 (Z_to_bv 64 GOT_INSTALL_BPF); C8 (Z_to_bv 64 (pk_oneshot PK)); C8 (Z_to_bv 64 GOT_BREAKLOOP); C8 (Z_to_bv 64 (pk_cleanup_sf PK))].
  Proof using Type. pin_using tt. intros R s CL FB m G. pose proof (GIo_core_misc _ _ _ _ _ G) as (_ & _ & _ & _ & _ & GOT). exact GOT. Qed.

  (* [comment removed for export] *)
  Lemma GIo_block_ok : forall R s CL FB m b, GIo R s CL FB m -> In b (CL ++ FB) -> block_ok (utp R) b.
  Proof using Type. pin_using tt. intros R s CL FB m b G Hin. destruct (GIo_blocks _ _ _ _ _ G) as [BO _]. exact (proj1 (Forall_forall _ _) BO b Hin). Qed.

  (* [comment removed for export] *)
  Lemma GIo_addr : heap_addr_law K HO -> forall R s CL FB m q A n,
    GIo R s CL FB m -> In (q, A, n) (CL ++ FB) -> ho_addr HO (ps_heap s) q = A.
  Proof using Type. pin_using tt. intros HAL R s CL FB m q A n G Hin. exact (HAL _ _ _ _ (q, A, n) (proj1 G) Hin). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma apart_sym : forall (b b' : cblk), apart b b' -> apart b' b.
  Proof using Type. pin_using tt. intros b b' Hab. unfold apart in *. lia. Qed.

  Lemma blocks_apart_perm : forall (L L' : list cblk), Permutation.Permutation L L' -> blocks_apart L -> blocks_apart L'.
  Proof using Type. pin_using tt.
    intros L L' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros HB.
    - exact HB.
    - destruct HB as [HF HB]. split; [|apply IH; exact HB].
      apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HF). eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP| exact Hb].
    - destruct HB as [HFy [HFx HB]]. apply Forall_cons_iff in HFy as [Ayx HFy].
      split; [apply Forall_cons; [apply apart_sym; exact Ayx| exact HFx]|]. split; [exact HFy| exact HB].
    - apply IH2, IH1, HB.
  Qed.

  Lemma blocks_ok_perm : forall u (L L' : list cblk), Permutation.Permutation L L' -> blocks_ok u L -> blocks_ok u L'.
  Proof using Type. pin_using tt.
    intros u L L' HP [BO BA]. split; [|eapply blocks_apart_perm; [exact HP| exact BA]].
    apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) BO). eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP| exact Hb].
  Qed.

  Lemma GIo_perm : heap_perm_law K -> forall R s CL CL' FB m, GIo R s CL FB m -> Permutation.Permutation CL CL' -> GIo R s CL' FB m.
  Proof using Type. pin_using tt.
    intros HPL R s CL CL' FB m (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW) HP.
    pose proof (Permutation.Permutation_app_tail FB HP) as HP'.
    split; [eapply HPL; [exact HH| exact HP']|]. split; [exact HS|]. split; [exact HA|]. split; [exact CT|]. split; [exact PT|].
    split; [exact CLI|]. split; [exact CM|]. split; [exact CE|]. split; [exact CS|]. split; [exact Etls|]. split; [exact TB|].
    split; [eapply blocks_ok_perm; [exact HP'| exact BOK]| exact SPW].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Lemma GIo_client_frame : forall R s CL FB m m' W,
    GIo R s CL FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W ->
    GIo R s CL FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CL FB m m' W G MU WM HW.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside W a).
    { intros a Ha H1 H2. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_client_frame_tls : forall R s CL FB m m' W tls',
    GIo R s CL FB m -> munch ((utp R, utp R + 256) :: W) m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W -> rw_cells ssegs m' (utp R) [CB 256 tls'] ->
    GIo R s CL FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CL FB m m' W tls' G MU WM HW HTLS.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> ~ (utp R <= a < utp R + 256) -> outside ((utp R, utp R + 256) :: W) a).
    { intros a Ha H1 H2 H3. cbn [outside]. split; [cbn [fst snd]; lia|].
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia| lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB| lia]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - exists tls'. exact HTLS.
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rw_cells_cut : forall m A cs k,
    rw_cells ssegs m A cs -> rw_cells ssegs m A (firstn k cs) /\ rw_cells ssegs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
  Proof using Type. pin_using tt. intros m A cs k HC. apply (proj1 (rw_cells_app ssegs m A _ _)). rewrite firstn_skipn. exact HC. Qed.

  Lemma rw_cells_uncut : forall m A cs1 cs2 A2,
    rw_cells ssegs m A cs1 -> rw_cells ssegs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells ssegs m A (cs1 ++ cs2).
  Proof using Type. pin_using tt. intros m A cs1 cs2 A2 HC1 HC2 ->. apply (proj2 (rw_cells_app ssegs m A _ _)). split; assumption. Qed.

  Definition set_pj_g (g : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) g (pj_h j) (pj_breakloop j).
  Definition set_pj_f (f : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) f (pj_g j) (pj_h j) (pj_breakloop j).
  Definition set_pj_h (h : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) (pj_g j) h (pj_breakloop j).

  Remark pc_pre_size : forall p P B rf j, csize rf = 8%nat -> cells_size (pc_pre p P B rf j) = 216%nat.
  Proof using Type. pin_using tt. intros p P B rf j Hrf. cbn. rewrite Hrf. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pcap_cells_split4 : forall m P p B rf st os j,
    csize rf = 8%nat ->
    rw_cells ssegs m P (pcap_cells_gen p P B rf st os j) ->
    rw_cells ssegs m P (pc_pre p P B rf j) /\ rw_cells ssegs m (P + 216) [CB 304 (pj_g j)]
    /\ rw_cells ssegs m (P + 520) (hdr_cells (pc_header p)) /\ rw_cells ssegs m (P + 544) (pc_ops p st os j).
  Proof using Type. pin_using tt.
    intros m P p B rf st os j Hrf HC. unfold pcap_cells_gen in HC.
    apply rw_cells_app in HC as [H1 HC]. rewrite (pc_pre_size p P B rf j Hrf) in HC.
    apply rw_cells_app in HC as [H2 HC]. cbn [cells_size csize Nat.add] in HC.
    apply rw_cells_app in HC as [H3 H4]. cbn [cells_size csize Nat.add hdr_cells] in H4.
    replace (P + Z.of_nat 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) in H4 by lia.
    replace (P + Z.of_nat 216 + Z.of_nat 304) with (P + 520) in H3 by lia.
    replace (P + Z.of_nat 216) with (P + 216) in H2 by lia. auto.
  Qed.

  Lemma pcap_cells_join4 : forall m P p B rf st os j cs h,
    csize rf = 8%nat ->
    rw_cells ssegs m P (pc_pre p P B rf j) -> rw_cells ssegs m (P + 216) cs -> cells_size cs = 304%nat ->
    rw_cells ssegs m (P + 520) (hdr_cells h) -> rw_cells ssegs m (P + 544) (pc_ops p st os j) ->
    rw_cells ssegs m P (pcap_cells_gen (set_header h p) P B rf st os (set_pj_g (cells_bytes cs) j)).
  Proof using Type. pin_using tt.
    intros m P p B rf st os j cs h Hrf H1 H2 Hcs H3 H4. unfold pcap_cells_gen.
    assert (E1 : pc_pre (set_header h p) P B rf (set_pj_g (cells_bytes cs) j) = pc_pre p P B rf j).
    { unfold pc_pre, np_entry, is_ng. destruct p; reflexivity. }
    assert (E2 : pc_ops (set_header h p) st os (set_pj_g (cells_bytes cs) j) = pc_ops p st os j).
    { unfold pc_ops, cleanup_entry, is_ng. destruct p; reflexivity. }
    rewrite E1, E2. replace (pc_header (set_header h p)) with h by (destruct p; reflexivity). cbn [pj_g set_pj_g].
    apply rw_cells_app. split; [exact H1|]. rewrite (pc_pre_size p P B rf j Hrf).
    pose proof (rw_cells_merge ssegs m (P + 216) [] cs (hdr_cells h ++ pc_ops p st os j)) as M. cbn [app] in M. rewrite Hcs in M.
    replace (P + Z.of_nat 216) with (P + 216) by lia. apply M.
    apply rw_cells_app. split; [exact H2|]. rewrite Hcs. apply rw_cells_app. split.
    - replace (P + 216 + Z.of_nat 304) with (P + 520) by lia. exact H3.
    - cbn [cells_size csize hdr_cells Nat.add]. replace (P + 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) by lia. exact H4.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_recell : forall m A cs cs',
    rw_cells ssegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells ssegs m A cs'.
  Proof using Type. pin_using tt.
    intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf'| rewrite Heq; exact Hb]|].
    rewrite <- (cells_bytes_length cs' Hwf'), Heq, (cells_bytes_length cs Hwf). exact Hw.
  Qed.

  (* [comment removed for export] *)
  Definition pack2 (lo hi : word) : word := Z_to_bv 64 (bv_unsigned lo mod 2^32 + 2^32 * (bv_unsigned hi mod 2^32)).
  Definition hdr3 (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C8 (pack2 (Z_to_bv 64 (h_caplen h)) (Z_to_bv 64 (h_len h)))].

  Lemma Z_to_le_bytes_split : forall a b z, (0 <= z)%Z ->
    Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
  Proof using Type. pin_using tt.
    induction a as [|a IH]; intros b z Hz.
    - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). f_equal. f_equal.
      rewrite Z.shiftr_shiftr by lia. f_equal. lia.
  Qed.

  Lemma le8_pack2 : forall lo hi, le8 (pack2 lo hi) = le4 lo ++ le4 hi.
  Proof using Type. pin_using tt.
    intros lo hi. unfold pack2, le8, le4, word_to_le_bytes.
    pose proof (Z.mod_pos_bound (bv_unsigned lo) (2^32) ltac:(lia)) as H1.
    pose proof (Z.mod_pos_bound (bv_unsigned hi) (2^32) ltac:(lia)) as H2.
    rewrite unsigned_lit by lia. change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_split by lia. f_equal.
    - rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned lo) 32) by (cbn; lia). f_equal.
      rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    - rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned hi) 32) by (cbn; lia). f_equal.
      change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma hdr3_bytes : forall h, cells_bytes (hdr3 h) = cells_bytes (hdr_cells h).
  Proof using Type. pin_using tt. intros h. cbn [cells_bytes cbytes hdr3 hdr_cells]. rewrite le8_pack2, <- app_assoc. reflexivity. Qed.

  Lemma hdr_cells_to_3 : forall m A h, rw_cells ssegs m A (hdr_cells h) -> rw_cells ssegs m A (hdr3 h).
  Proof using Type. pin_using tt. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | apply hdr3_bytes]. Qed.
  Lemma hdr_cells_of_3 : forall m A h, rw_cells ssegs m A (hdr3 h) -> rw_cells ssegs m A (hdr_cells h).
  Proof using Type. pin_using tt. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | symmetry; apply hdr3_bytes]. Qed.

  (* [comment removed for export] *)
  Lemma PCAPRg_blocks : forall P p PB rf st os m, PCAPRg P p PB rf st os m ->
    exists B I, PB = pcap_blocks p P B I.
  Proof using Type. pin_using tt. intros P p PB rf st os m (B & I & j & pad & bs & E & _). exists B, I. exact E. Qed.

  Lemma PCAPR_self_in : forall P p PB FB m, PCAPR P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof using Type. pin_using tt. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.

  Lemma psize_pos : forall p, 664 <= psize p <= 680.
  Proof using Type. pin_using tt. intros p. unfold psize, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL. destruct (is_ng p); lia. Qed.

  (* [comment removed for export] *)
  Definition pcap_iv (R : rctx) (PB : list cblk) (iv : Z * Z) : Prop :=
    (rc_lo R <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block PB iv.

  Lemma GIo_pcap_frame : forall R s CLc PB FB m m' W,
    GIo R s (CLc ++ PB) FB m -> munch W m m' -> wmono ssegs m m' -> Forall (pcap_iv R PB) W ->
    GIo R s (CLc ++ PB) FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CLc PB FB m m' W G MU WM HW. eapply GIo_client_frame; [exact G|exact MU|exact WM|].
    apply Forall_impl with (2 := HW). intros iv [Hs|Hb]; [left; exact Hs| right].
    unfold iv_in_block in *. rewrite Exists_app. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_pcap_writes : forall R s CLc PB FB m m' W SP,
    GIo R s (CLc ++ PB) FB m -> munch W m m' -> wmono ssegs m m' ->
    Forall (fun iv => (rc_lo R <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv) W -> rc_lo R <= SP ->
    agrees_on (client_keeps CLc SP) m m'.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m m' W SP G MU WM HW HSP.
    pose proof (GIo_blocks _ _ _ _ _ G) as [BO BA]. pose proof (GIo_spw _ _ _ _ _ G) as SPW.
    apply blocks_apart_app_inv in BA as (BA1 & _ & _). apply blocks_apart_app_inv in BA1 as (_ & _ & BAX).
    apply Forall_app in BO as [BO _]. apply Forall_app in BO as [BOc BOp].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hlo|Hb]; cbn [fst snd] in *.
    - destruct Hk as [Hk|Hk]; [lia|]. apply in_block_In in Hk as (b & Hbin & Hb).
      pose proof (proj1 (Forall_forall _ _) BOc b Hbin) as (K1 & K2 & K3 & K4 & K5 & K6). unfold rc_lo in HSP, Hlo.
      unfold cb_addr, cb_size in *. lia.
    - unfold iv_in_block in Hb. apply Exists_exists in Hb as (b' & Hb'in & Hlo' & Hhi'). cbn [fst snd] in Hlo', Hhi'.
      pose proof (proj1 (Forall_forall _ _) BOp b' Hb'in) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Hk as [Hk|Hk]; [unfold rc_lo in HSP; lia|]. apply in_block_In in Hk as (b & Hbin & Hb).
      pose proof (BAX b b' Hbin Hb'in) as AP. unfold apart in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_PB_block : forall R s CLc PB FB m q A n, GIo R s (CLc ++ PB) FB m -> In (q, A, n) PB ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x55000 <= A)
    /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m q A n G Hin.
    pose proof (GIo_block_ok _ _ _ _ _ (q, A, n) G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hin)) as (K1 & K2 & K3 & K4 & K5 & K6).
    cbn [cb_addr cb_size fst snd] in *. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_apart : forall R s CL FB m b b', GIo R s CL FB m -> In b (CL ++ FB) -> In b' (CL ++ FB) -> b = b' \/ apart b b'.
  Proof using Type. pin_using tt. intros R s CL FB m b b' G H1 H2. exact (blocks_apart_In _ _ _ (proj2 (GIo_blocks _ _ _ _ _ G)) H1 H2). Qed.

  (* [comment removed for export] *)
  Lemma sp_above_blocks : forall (sp : word) R s CL FB m lo budget (tp : word),
    std_pre_o sp tp R s CL FB lo budget m -> 0 <= budget -> CEILZ <= bv_unsigned sp - budget /\ bv_unsigned sp <= rc_spmain R /\ 0x7fff80000000 <= usp0 R.
  Proof using Type. pin_using tt.
    intros sp R s CL FB m lo budget tp (G & ST & LO & BU & SPM & MI & TP & ALN) Hb.
    pose proof (GIo_spw _ _ _ _ _ G) as [SPWa SPWb]. unfold rc_lo in LO. split; [lia|]. split; [exact SPM| exact SPWa].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma priv_cells_size : forall p I pad, length pad = 4%nat ->
    cells_size (priv_cells p I pad) = (if is_ng p then 32 else 16)%nat.
  Proof using Type. pin_using tt. intros p I pad Hp. unfold priv_cells, is_ng. destruct (pc_priv p); cbn; reflexivity. Qed.

  Lemma priv_cells_size_le : forall m P p I pad, rw_cells ssegs m P (priv_cells p I pad) -> (Z.of_nat (cells_size (priv_cells p I pad)) <= 32)%Z.
  Proof using Type. pin_using tt.
    intros m P p I pad [[Hwf _] _]. unfold priv_cells in *. destruct (pc_priv p); cbn in *; [lia|].
    destruct Hwf as (_ & _ & _ & _ & Hl & _). cbn in Hl. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PB_apart : forall R s CLc PB FB m p P B I,
    GIo R s (CLc ++ PB) FB m -> PB = pcap_blocks p P B I ->
    (P + psize p <= B \/ B + pc_bufalloc p <= P)
    /\ (forall sg q, pc_priv p = PrivNg sg (Some q) ->
          (P + psize p <= I \/ I + 40 * ng_ifaces_size sg <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size sg <= B)).
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m p P B I G EPB.
    pose proof (proj2 (GIo_blocks _ _ _ _ _ G)) as BA.
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    rewrite EPB in BA. unfold pcap_blocks in BA. cbn [blocks_apart] in BA.
    destruct BA as (F1 & F2 & _). pose proof (Forall_inv F1) as A12. apply Forall_inv_tail in F1.
    unfold apart, cb_addr, cb_size in A12; cbn [fst snd] in A12. split; [lia|].
    intros sg q Hq. rewrite Hq in F1, F2. pose proof (Forall_inv F1) as A13. pose proof (Forall_inv F2) as A23.
    unfold apart, cb_addr, cb_size in A13, A23; cbn [fst snd] in A13, A23. lia.
  Qed.

  Lemma if_cells_size : forall i j, cells_size (if_cells i j) = 40%nat.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma ifs_cells_size : forall ifs js, length js = length ifs -> cells_size (ifs_cells ifs js) = (40 * length ifs)%nat.
  Proof using Type. pin_using tt.
    induction ifs as [|i ifs IH]; intros [|j0 js0] Hlen; cbn [length] in Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [ifs_cells]. rewrite cells_size_app, if_cells_size, (IH js0) by lia. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ifaces_ok_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_ok p I m -> ifaces_ok p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p I m m' Q AG HQ IFS. unfold ifaces_ok in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as (js & tail & Hl & HC & H1 & H2 & H3 & H4). exists js, tail. split; [exact Hl|]. split; [|repeat split; try assumption; lia].
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl).
    pose proof (rw_cells_bound _ _ _ _ HC) as HB.
    rewrite cells_size_app in Ha, HB. cbn [cells_size csize] in Ha, HB. rewrite Nat.add_0_r in Ha, HB.
    rewrite ifs_cells_size in Ha by (rewrite length_rev; lia). rewrite length_rev in Ha. lia.
  Qed.

  Lemma priv_cells_psize : forall m A p I pad, rw_cells ssegs m A (priv_cells p I pad) ->
    Z.of_nat (cells_size (priv_cells p I pad)) = psize p - PCAP_PRIV_OFF.
  Proof using Type. pin_using tt.
    intros m A p I pad [[Hwf _] _]. unfold priv_cells, psize, is_ng, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL in *.
    destruct (pc_priv p); cbn in *; lia.
  Qed.

  Lemma pcap_aux_agree : forall p P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a) ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a) ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    0 <= pc_bufalloc p ->
    rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_ok p I m ->
    rw_cells ssegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells ssegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_ok p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_ok_agree; eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma pcap_cells_gen_size : forall p P B rf st os j, csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    cells_size (pcap_cells_gen p P B rf st os j) = 648%nat.
  Proof using Type. pin_using tt. intros p P B rf st os j H1 H2 H3. unfold pcap_cells_gen. rewrite !cells_size_app. cbn. rewrite H1, H2, H3. reflexivity. Qed.


  (* [comment removed for export] *)
  Lemma PCAPRg_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg P p PB rf st os m -> PCAPRg P p PB rf st os m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_ok_agree; [exact AG| exact Q3| exact IFS].
  Qed.

  Lemma PCAPR_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR P p PB FB m -> PCAPR P p PB FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ifaces_ok_closable : forall p I m, ifaces_ok p I m -> ifaces_closable p I m.
  Proof using Type. pin_using tt.
    intros p I m HI. unfold ifaces_ok, ifaces_closable in *. destruct (pc_priv p) as [sf|s [q|]]; [exact HI| |tauto].
    destruct HI as (js & tail & Ljs & CE & E1 & E2 & E3 & E4). split; [|exact E3].
    rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail]), app_assoc in CE.
    apply (rw_cells_merge ssegs m I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
    cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in CE by lia.
    eexists. exact CE.
  Qed.
  Lemma PCAPR_closable_of : forall P p PB FB m, PCAPR P p PB FB m -> PCAPR_closable P p PB FB m.
  Proof using Type. pin_using tt.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    exists Af. split; [exact Hin|]. exists B, I, j, pad, bs. repeat (split; [assumption|]). split; [apply ifaces_ok_closable; exact IFS| exact WF].
  Qed.

  Lemma ifaces_closable_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_closable p I m -> ifaces_closable p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p I m m' Q AG HQ IFS. unfold ifaces_closable in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as ((junk & HC) & H3). split; [|exact H3]. exists junk.
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl). cbn [cells_size csize] in Ha. lia.
  Qed.
  Lemma PCAPRg_closable_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg_closable P p PB rf st os m -> PCAPRg_closable P p PB rf st os m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_closable_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  Lemma PCAPR_closable_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR_closable P p PB FB m -> PCAPR_closable P p PB FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_closable_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_new_file_not_out : heap_addr_law K HO -> forall R s s2 CL CL2 FB f Af m m2,
    GIo R s CL FB m -> GIo R s2 CL2 ((f, Af, FILE_BLOCK) :: FB) m2 -> ps_outfile s2 = ps_outfile s -> ps_outfile s2 <> Some f.
  Proof using Type. pin_using tt.
    intros HAL R s s2 CL CL2 FB f Af m m2 G G2 E C.
    pose proof (proj1 (proj2 (proj2 G))) as HR. rewrite <- E, C in HR. destruct HR as (_ & _ & (A & HinA & _)).
    pose proof (GIo_addr HAL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as E1.
    pose proof (GIo_addr HAL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; right; exact HinA)) as E2.
    pose proof (GIo_blocks _ _ _ _ _ G2) as [_ BA]. apply blocks_apart_app_inv in BA as (_ & BA & _).
    destruct BA as [HF _]. apply (proj1 (Forall_forall _ _) HF) in HinA. unfold apart, FILE_BLOCK in HinA. cbn [cb_addr cb_size fst snd] in HinA. lia.
  Qed.

  Lemma in_PB_below : forall R s CLc PB FB m a, GIo R s (CLc ++ PB) FB m -> in_block PB a -> 0 < a < CEILZ.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m a G Hin. apply in_block_In in Hin as ([[q A] n] & HbIn & Hb). cbn [cb_addr cb_size fst snd] in Hb.
    pose proof (GIo_PB_block _ _ _ _ _ _ _ _ _ G HbIn) as (K1 & K2 & K3 & K4 & K5 & K6). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_CLc_facts : forall R s CLc PB FB m a, GIo R s (CLc ++ PB) FB m -> in_block CLc a -> 0 < a < CEILZ /\ ~ in_block PB a.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m a G Hin. pose proof (GIo_blocks _ _ _ _ _ G) as [BO BA].
    apply Forall_app in BO as [BO _]. apply Forall_app in BO as [BOc BOp].
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & _ & BAX).
    split; [destruct (in_block_facts _ _ _ BOc Hin) as (F1 & F2 & _); lia|].
    intros Hin'. apply in_block_In in Hin as (b & Hb & Hr). apply in_block_In in Hin' as (b' & Hb' & Hr').
    pose proof (BAX b b' Hb Hb') as AP. unfold apart in AP. lia.
  Qed.

  Lemma pcap_wf_set_header : forall p h, pcap_wf p -> 0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 -> pcap_wf (set_header h p).
  Proof using Type. pin_using tt. intros p h WF Hc Hl. unfold pcap_wf in *. destruct p; cbn in *. repeat split; try lia; tauto. Qed.

  (* [comment removed for export] *)
  Lemma PCAPR_intro_set_header : forall P p PB FB m h Af B I j pad bs,
    In (pc_rfile p, Af, FILE_BLOCK) FB -> PB = pcap_blocks p P B I ->
    rw_cells ssegs m P (pcap_cells_gen (set_header h p) P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j) ->
    rw_cells ssegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> rw_cells ssegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
    firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> ifaces_ok p I m -> pcap_wf p ->
    0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 ->
    PCAPR P (set_header h p) PB FB m.
  Proof using Type. pin_using tt.
    intros P p PB FB m h Af B I j pad bs Hin EPB HC HP HB PFX IFS WF Hc Hl.
    pose proof (pcap_wf_set_header p h WF Hc Hl) as WF'.
    exists Af. split; [destruct p; exact Hin|]. exists B, I, j, pad, bs.
    split; [destruct p; exact EPB|]. split; [exact HC|]. split; [destruct p; exact HP|]. split; [destruct p; exact HB|].
    split; [destruct p; exact PFX|]. split; [destruct p; exact IFS| exact WF'].
  Qed.
End Rep.
End WithCeil.

Arguments pcap_junk : clear implicits.
Arguments if_junk : clear implicits.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Record pcap_consts := mkPK {
  pk_next_pcap : Z;     (* [comment removed for export] *)
  pk_next_ng : Z;       (* [comment removed for export] *)
  pk_cleanup_sf : Z;    (* [comment removed for export] *)
  pk_cleanup_ng : Z;    (* [comment removed for export] *)
  pk_oneshot : Z;       (* [comment removed for export] *)
  pk_stats : Z          (* [comment removed for export] *)
}.
Definition PK : pcap_consts := mkPK 0x1596c 0x17a04 0x1422c 0x1828c 0x147dc 0x1475c.

(* [comment removed for export] *)
Definition PCAP_NEXT_EX_ENTRY : Z := 0x14820.
Definition PCAP_OFFLINE_READ_ENTRY : Z := 0x145a4.
Definition PCAP_STATS_ENTRY : Z := 0x14a4c.
Definition PCAP_CLOSE_ENTRY : Z := 0x148a4.
Definition PCAP_FREECODE_ENTRY : Z := 0x14798.
Definition PCAP_OPEN_OFFLINE_ENTRY : Z := 0x14580.
Definition PCAP_OPEN_OFFLINE_WTP_ENTRY : Z := 0x14284.
Definition PCAP_FOPEN_OFFLINE_WTP_ENTRY : Z := 0x14398.
Definition PCAP_OPEN_OFFLINE_COMMON_ENTRY : Z := 0x148f4.
Definition PCAP_CHECK_HEADER_ENTRY : Z := 0x15478.
Definition PCAP_NG_CHECK_HEADER_ENTRY : Z := 0x16ac8.
Definition PCAP_ADJUST_SNAPSHOT_ENTRY : Z := 0x1458c.
Definition LINKTYPE_TO_DLT_ENTRY : Z := 0x15ed0.
Definition MAX_SNAPLEN_ENTRY : Z := 0x15f0c.
Definition PCAP_POST_PROCESS_ENTRY : Z := 0x15f44.
Definition PCAP_STRERROR_ENTRY : Z := 0x149a0.
Definition PCAP_FMT_ERRMSG_ENTRY : Z := 0x14a80.
Definition READ_BYTES_ENTRY : Z := 0x1703c.
Definition READ_BLOCK_ENTRY : Z := 0x17124.
Definition ADD_INTERFACE_ENTRY : Z := 0x17524.

(* [comment removed for export] *)
Definition GOT_PCAP_ADDR : Z := 0x22d90.
Definition GOT_INSTALL_BPF : Z := 0x14b64.
Definition GOT_BREAKLOOP : Z := 0x14a64.

(* [comment removed for export] *)
Definition FILE_BLOCK : Z := 1264.    (* [comment removed for export] *)
Definition PCAP_HDR_OFF : Z := 520.   (* [comment removed for export] *)
Definition PCAP_ERRBUF_OFF : Z := 216.
Definition PCAP_PRIV_OFF : Z := 648.  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma eqz_false : forall z, (0 < z < 2^64)%Z -> bv_eqb (Z_to_bv 64 z) z64 = false.
Proof using Type. pin_using tt. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.
Lemma nez_true : forall z, (0 < z < 2^64)%Z -> negb (bv_eqb (Z_to_bv 64 z) z64) = true.
Proof using Type. pin_using tt. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. Qed.
Lemma eqb_lits_false : forall x y, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> x <> y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using Type. pin_using tt. intros x y Hx Hy Hne. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

(* [comment removed for export] *)
Lemma and7_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 8 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0%Z.
Proof using Type. pin_using tt.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Ha.
Qed.
Lemma and3_aligned : forall x, (0 <= x < 2^64)%Z -> (x mod 4 = 0)%Z -> Z.land (bv_unsigned (Z_to_bv 64 x)) 3 = 0%Z.
Proof using Type. pin_using tt.
  intros x Hx Ha. rewrite unsigned_lit by lia. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2)%Z with 4%Z. exact Ha.
Qed.
Lemma aligned16_8 : forall x k, (x mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((x + k) mod 8 = 0)%Z.
Proof using Type. pin_using tt.
  intros x k Hx Hk. rewrite Z.add_mod, Hk, Z.add_0_r by lia. rewrite Z.mod_mod by lia.
  apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q ->]. replace (q * 16)%Z with ((q * 2) * 8)%Z by lia. apply Z.mod_mul.
  all: lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rep.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  #[local] Abbreviation pcapT := (PcapTypes.pcap hptr hptr).

  Definition b8 (z : Z) : byte := Z_to_bv 8 z.

  Definition is_ng (p : pcapT) : bool := match pc_priv p with PrivNg _ _ => true | PrivPcap _ => false end.
  Definition np_entry (p : pcapT) : Z := if is_ng p then pk_next_ng PK else pk_next_pcap PK.
  Definition cleanup_entry (p : pcapT) : Z := if is_ng p then pk_cleanup_ng PK else pk_cleanup_sf PK.
  (* [comment removed for export] *)
  Definition psize (p : pcapT) : Z := if is_ng p then PCAP_NG_SF_TOTAL else PCAP_SF_TOTAL.

  (* [comment removed for export] *)
  Definition hdr_cells (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C4 (Z_to_bv 64 (h_caplen h)); C4 (Z_to_bv 64 (h_len h))].

  (* [comment removed for export] *)
  Record pcap_junk := mkPJ {
    pj_read_op : word;      (* [comment removed for export] *)
    pj_fd : word;           (* [comment removed for export] *)
    pj_a : list byte;       (* [comment removed for export] *)
    pj_b : list byte;       (* [comment removed for export] *)
    pj_c : list byte;       (* [comment removed for export] *)
    pj_d : list byte;       (* [comment removed for export] *)
    pj_e : list byte;       (* [comment removed for export] *)
    pj_f : list byte;       (* [comment removed for export] *)
    pj_g : list byte;       (* [comment removed for export] *)
    pj_h : list byte;       (* [comment removed for export] *)
    pj_breakloop : word     (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pc_pre (p : pcapT) (P B : Z) (rf : cell) (j : pcap_junk) : list cell :=
    [ C8 (pj_read_op j);                         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (np_entry p));              (* [comment removed for export] *)
      C4 (pj_fd j);                              (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_bufsize p));            (* [comment removed for export] *)
      C8 (Z_to_bv 64 B);                         (* [comment removed for export] *)
      CB 12 (pj_a j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_break_loop p));         (* [comment removed for export] *)
      C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF));       (* [comment removed for export] *)
      C4 (Z_to_bv 64 (Z.b2z (pc_swapped p)));    (* [comment removed for export] *)
      CB 4 (pj_b j);                             (* [comment removed for export] *)
      rf;                                        (* [comment removed for export] *)
      CB 16 (pj_c j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_major p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_version_minor p));      (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_snapshot p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype p));           (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_linktype_ext p));       (* [comment removed for export] *)
      CB 12 (pj_d j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0);                         (* [comment removed for export] *)
      CB 28 (pj_e j);                            (* [comment removed for export] *)
      C4 (Z_to_bv 64 (pc_tstamp_precision p));   (* [comment removed for export] *)
      CB 48 (pj_f j);                            (* [comment removed for export] *)
      C8 (Z_to_bv 64 0) ].                       (* [comment removed for export] *)
  Definition pc_ops (p : pcapT) (st os : cell) (j : pcap_junk) : list cell :=
    [ CB 72 (pj_h j);                            (* [comment removed for export] *)
      st;                                        (* [comment removed for export] *)
      C8 (pj_breakloop j);                       (* [comment removed for export] *)
      os;                                        (* [comment removed for export] *)
      C8 (Z_to_bv 64 (cleanup_entry p)) ].       (* [comment removed for export] *)
  Definition pcap_cells_gen (p : pcapT) (P B : Z) (rf st os : cell) (j : pcap_junk) : list cell :=
    pc_pre p P B rf j ++ [CB 304 (pj_g j)] (* [comment removed for export] *) ++ hdr_cells (pc_header p) (* [comment removed for export] *) ++ pc_ops p st os j.

  Definition pcap_cells (p : pcapT) (P B Af : Z) (j : pcap_junk) : list cell :=
    pcap_cells_gen p P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j.

  Remark pcap_cells_size : forall p P B Af j, cells_size (pcap_cells p P B Af j) = 648%nat.
  Proof using Type. pin_using tt. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition lenswap_code (l : lenswap_t) : Z := match l with NOT_SWAPPED => 0 | SWAPPED => 1 | MAYBE_SWAPPED => 2 end.
  Definition sfscale_code (t : sf_scale_t) : Z := match t with SF_PASS_THROUGH => 0 | SF_SCALE_UP => 1 | SF_SCALE_DOWN => 2 end.
  Definition ngscale_code (t : ng_scale_t) : Z :=
    match t with NG_PASS_THROUGH => 0 | SCALE_UP_DEC => 1 | SCALE_DOWN_DEC => 2 | SCALE_UP_BIN => 3 | SCALE_DOWN_BIN => 4 end.
  Definition is_dec (t : ng_scale_t) : bool := match t with SCALE_UP_DEC | SCALE_DOWN_DEC => true | _ => false end.

  (* [comment removed for export] *)
  Definition sf_cells (s : pcap_sf) : list cell :=
    [C8 (Z_to_bv 64 (sf_hdrsize s)); C4 (Z_to_bv 64 (lenswap_code (sf_lengths_swapped s))); C4 (Z_to_bv 64 (sfscale_code (sf_scale_type s)))].
  (* [comment removed for export] *)
  Definition ng_cells (s : pcap_ng_sf) (I : Z) (pad : list byte) : list cell :=
    [C8 (Z_to_bv 64 (ng_user_tsresol s)); C4 (Z_to_bv 64 (ng_max_blocksize s)); C4 (Z_to_bv 64 (ng_ifcount s));
     C4 (Z_to_bv 64 (ng_ifaces_size s)); CB 4 pad; C8 (Z_to_bv 64 I)].
  Definition priv_cells (p : pcapT) (I : Z) (pad : list byte) : list cell :=
    match pc_priv p with PrivPcap s => sf_cells s | PrivNg s _ => ng_cells s I pad end.

  (* [comment removed for export] *)
  Record if_junk := mkIJ { ij_p1 : list byte; ij_p2 : list byte; ij_sf : word }.
  Definition if_cells (i : ng_if) (j : if_junk) : list cell :=
    [C4 (Z_to_bv 64 (if_snaplen i)); CB 4 (ij_p1 j); C8 (Z_to_bv 64 (if_tsresol i)); C4 (Z_to_bv 64 (ngscale_code (if_scale_type i)));
     CB 4 (ij_p2 j); C8 (if is_dec (if_scale_type i) then Z_to_bv 64 (if_scale_factor i) else ij_sf j); C8 (Z_to_bv 64 (if_tsoffset i))].
  Fixpoint ifs_cells (ifs : list ng_if) (js : list if_junk) : list cell :=
    match ifs, js with
    | i :: ifs', j :: js' => if_cells i j ++ ifs_cells ifs' js'
    | _, _ => []
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition if_wf (i : ng_if) : Prop :=
    0 < if_tsresol i < 2^64 /\ (is_dec (if_scale_type i) = true -> 0 < if_scale_factor i < 2^64).

  Definition ifaces_ok (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0 /\ ng_ifaces s = [] /\ ng_ifcount s = 0 /\ ng_ifaces_size s = 0
    | PrivNg s (Some q) =>
        exists js tail, length js = length (ng_ifaces s)
          /\ rw_cells usegs m I (ifs_cells (rev (ng_ifaces s)) js ++ [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail])
          /\ ng_ifcount s = Z.of_nat (length (ng_ifaces s)) /\ ng_ifcount s <= ng_ifaces_size s /\ 1 <= ng_ifaces_size s < 2^26
          /\ Forall if_wf (ng_ifaces s)
    end.

  (* [comment removed for export] *)
  Definition pcap_blocks (p : pcapT) (P B I : Z) : list cblk :=
    (pc_self p, P, psize p) :: (pc_buffer p, B, pc_bufalloc p)
    :: match pc_priv p with
       | PrivNg s (Some q) => [(q, I, 40 * ng_ifaces_size s)]
       | _ => []
       end.

  (* [comment removed for export] *)
  Definition pcap_wf (p : pcapT) : Prop :=
    1 <= pc_snapshot p <= INT_MAX
    /\ 0 <= pc_bufsize p <= 2^30 /\ 0 <= pc_bufalloc p < 2^32
    /\ Z.of_nat (length (pc_bufdata p)) <= pc_bufalloc p
    /\ pc_break_loop p = 0 /\ pc_tstamp_precision p = 0
    /\ 0 <= pc_version_major p < 2^16 /\ 0 <= pc_version_minor p < 2^16
    /\ 0 <= pc_linktype p < 2^31 /\ -2^31 <= pc_linktype_ext p < 2^31
    /\ 0 <= h_caplen (pc_header p) < 2^32 /\ 0 <= h_len (pc_header p) < 2^32
    /\ match pc_priv p with
       | PrivPcap s => sf_hdrsize s = 16 \/ sf_hdrsize s = 24
       | PrivNg s _ => 0 < ng_user_tsresol s < 2^64 /\ 0 <= ng_max_blocksize s <= 2^30 /\ 0 <= ng_ifcount s < 2^32 /\ 0 <= ng_ifaces_size s < 2^32
       end
    /\ pc_bufsize p <= pc_bufalloc p.          (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PCAPRg (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells usegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_ok p I m
    /\ pcap_wf p.

  (* [comment removed for export] *)
  Definition PCAPR (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.

  (* [comment removed for export] *)
  Definition pre_PCAPR (P : Z) (p : pcapT) (PB : list cblk) (m : mem) : Prop :=
    exists rf st os, length rf = 8%nat /\ length st = 8%nat /\ length os = 8%nat /\ PCAPRg P p PB (CB 8 rf) (CB 8 st) (CB 8 os) m.

  (* [comment removed for export] *)
  Definition ifaces_closable (p : pcapT) (I : Z) (m : mem) : Prop :=
    match pc_priv p with
    | PrivPcap _ => I = 0
    | PrivNg s None => I = 0
    | PrivNg s (Some q) => (exists junk, rw_cells usegs m I [CB (Z.to_nat (40 * ng_ifaces_size s)) junk]) /\ 1 <= ng_ifaces_size s < 2^26
    end.
  Definition PCAPRg_closable (P : Z) (p : pcapT) (PB : list cblk) (rf st os : cell) (m : mem) : Prop :=
    exists (B I : Z) (j : pcap_junk) (pad : list byte) (bs : list byte),
       PB = pcap_blocks p P B I
    /\ rw_cells usegs m P (pcap_cells_gen p P B rf st os j)
    /\ rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad)
    /\ rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs]
    /\ firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p)
    /\ ifaces_closable p I m
    /\ pcap_wf p.
  Definition PCAPR_closable (P : Z) (p : pcapT) (PB FB : list cblk) (m : mem) : Prop :=
    exists Af, In (pc_rfile p, Af, FILE_BLOCK) FB
      /\ PCAPRg_closable P p PB (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) m.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition GIo (R : rctx) (s : PS) (CL FB : list cblk) (m : mem) : Prop :=
       mk_heap K (ps_heap s) R (CL ++ FB) m
    /\ mk_stdio K (ps_libc s) R FB m
    /\ HARNR (ps_outfile s) FB m
    /\ CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m
    /\ ps_tls s = utp R - 200 /\ tls_block_ok_u (utp R - 200)
    /\ blocks_ok (utp R) (CL ++ FB)
    /\ 0x7fff80000000 <= usp0 R <= 2^47
    /\ CEILZ <= rc_lo R.                      (* [comment removed for export] *)

  Lemma GI_open : forall R s CL m, GI K R s CL m <-> exists FB, GIo R s CL FB m.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma GIo_close : forall R s CL FB m, GIo R s CL FB m -> GI K R s CL m.
  Proof using Type. pin_using tt. intros R s CL FB m G. exists FB. exact G. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition std_pre_o (sp tp : word) (R : rctx) (s : PS) (CL FB : list cblk) (lo budget : Z) (m : mem) : Prop :=
    GIo R s CL FB m /\ stk usegs m lo (bv_unsigned sp) /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp
    /\ bv_unsigned sp <= rc_spmain R /\ mem_inv usegs m /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0.

  Lemma std_pre_o_close : forall sp tp R s CL FB lo budget m,
    std_pre_o sp tp R s CL FB lo budget m -> std_pre K sp tp R s CL lo budget m.
  Proof using Type. pin_using tt.
    intros sp tp R s CL FB lo budget m (G & A & B & C & D & E & F & AL). unfold std_pre.
    split; [eapply GIo_close; exact G|]. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact F| exact AL].
  Qed.

  Lemma aln16_add : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a + k) mod 16 = 0.
  Proof using Type. pin_using tt. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma GIo_blocks : forall R s CL FB m, GIo R s CL FB m -> blocks_ok (utp R) (CL ++ FB).
  Proof using Type. pin_using tt. intros R s CL FB m G. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 G)))))))))))). Qed.

  Lemma GIo_tls : forall R s CL FB m, GIo R s CL FB m -> ps_tls s = utp R - 200 /\ tls_block_ok_u (utp R - 200).
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & E & T & _). auto. Qed.

  (* [comment removed for export] *)
  Lemma GIo_spw : forall R s CL FB m, GIo R s CL FB m -> 0x7fff80000000 <= usp0 R /\ CEILZ <= usp0 R - 8388608.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & C). unfold rc_lo in C. exact (conj (proj1 W) C). Qed.
  Lemma GIo_sp47 : forall R s CL FB m, GIo R s CL FB m -> usp0 R <= 2^47.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W & _). exact (proj2 W). Qed.
  Lemma GIo_ceil_lo : forall R s CL FB m, GIo R s CL FB m -> CEILZ <= rc_lo R.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C). exact C. Qed.

  Lemma GIo_pcap_tls : forall R s CL FB m, GIo R s CL FB m -> PCAP_TLS R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & PT & _). exact PT. Qed.

  Lemma GIo_core_tls : forall R s CL FB m, GIo R s CL FB m -> CORE_TLS R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & CT & _). exact CT. Qed.

  Lemma GIo_core_misc : forall R s CL FB m, GIo R s CL FB m -> CORE_MISC m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & _ & CM & _). exact CM. Qed.

  Lemma GIo_core_libc : forall R s CL FB m, GIo R s CL FB m -> CORE_LIBC R m.
  Proof using Type. pin_using tt. intros R s CL FB m (_ & _ & _ & _ & _ & CLI & _). exact CLI. Qed.

  (* [comment removed for export] *)
  Lemma GIo_got_pcap : forall R s CL FB m, GIo R s CL FB m ->
    rw_cells usegs m GOT_PCAP_ADDR [C8 (Z_to_bv 64 GOT_INSTALL_BPF); C8 (Z_to_bv 64 (pk_oneshot PK)); C8 (Z_to_bv 64 GOT_BREAKLOOP); C8 (Z_to_bv 64 (pk_cleanup_sf PK))].
  Proof using Type. pin_using tt. intros R s CL FB m G. pose proof (GIo_core_misc _ _ _ _ _ G) as (_ & _ & _ & _ & _ & GOT). exact GOT. Qed.

  (* [comment removed for export] *)
  Lemma GIo_block_ok : forall R s CL FB m b, GIo R s CL FB m -> In b (CL ++ FB) -> block_ok (utp R) b.
  Proof using Type. pin_using tt. intros R s CL FB m b G Hin. destruct (GIo_blocks _ _ _ _ _ G) as [BO _]. exact (proj1 (Forall_forall _ _) BO b Hin). Qed.

  (* [comment removed for export] *)
  Lemma GIo_addr : heap_addr_law K HO -> forall R s CL FB m q A n,
    GIo R s CL FB m -> In (q, A, n) (CL ++ FB) -> ho_addr HO (ps_heap s) q = A.
  Proof using Type. pin_using tt. intros HAL R s CL FB m q A n G Hin. exact (HAL _ _ _ _ (q, A, n) (proj1 G) Hin). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma apart_sym : forall (b b' : cblk), apart b b' -> apart b' b.
  Proof using Type. pin_using tt. intros b b' Hab. unfold apart in *. lia. Qed.

  Lemma blocks_apart_perm : forall (L L' : list cblk), Permutation.Permutation L L' -> blocks_apart L -> blocks_apart L'.
  Proof using Type. pin_using tt.
    intros L L' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros HB.
    - exact HB.
    - destruct HB as [HF HB]. split; [|apply IH; exact HB].
      apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HF). eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP| exact Hb].
    - destruct HB as [HFy [HFx HB]]. apply Forall_cons_iff in HFy as [Ayx HFy].
      split; [apply Forall_cons; [apply apart_sym; exact Ayx| exact HFx]|]. split; [exact HFy| exact HB].
    - apply IH2, IH1, HB.
  Qed.

  Lemma blocks_ok_perm : forall u (L L' : list cblk), Permutation.Permutation L L' -> blocks_ok u L -> blocks_ok u L'.
  Proof using Type. pin_using tt.
    intros u L L' HP [BO BA]. split; [|eapply blocks_apart_perm; [exact HP| exact BA]].
    apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) BO). eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HP| exact Hb].
  Qed.

  Lemma GIo_perm : heap_perm_law K -> forall R s CL CL' FB m, GIo R s CL FB m -> Permutation.Permutation CL CL' -> GIo R s CL' FB m.
  Proof using Type. pin_using tt.
    intros HPL R s CL CL' FB m (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW) HP.
    pose proof (Permutation.Permutation_app_tail FB HP) as HP'.
    split; [eapply HPL; [exact HH| exact HP']|]. split; [exact HS|]. split; [exact HA|]. split; [exact CT|]. split; [exact PT|].
    split; [exact CLI|]. split; [exact CM|]. split; [exact CE|]. split; [exact CS|]. split; [exact Etls|]. split; [exact TB|].
    split; [eapply blocks_ok_perm; [exact HP'| exact BOK]| exact SPW].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Lemma GIo_client_frame : forall R s CL FB m m' W,
    GIo R s CL FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W ->
    GIo R s CL FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CL FB m m' W G MU WM HW.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside W a).
    { intros a Ha H1 H2. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_client_frame_tls : forall R s CL FB m m' W tls',
    GIo R s CL FB m -> munch ((utp R, utp R + 256) :: W) m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W -> rw_cells usegs m' (utp R) [CB 256 tls'] ->
    GIo R s CL FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CL FB m m' W tls' G MU WM HW HTLS.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> ~ (utp R <= a < utp R + 256) -> outside ((utp R, utp R + 256) :: W) a).
    { intros a Ha H1 H2 H3. cbn [outside]. split; [cbn [fst snd]; lia|].
      eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia| lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB| lia]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - exists tls'. exact HTLS.
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia|lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia|lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rw_cells_cut : forall m A cs k,
    rw_cells usegs m A cs -> rw_cells usegs m A (firstn k cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
  Proof using Type. pin_using tt. intros m A cs k HC. apply (proj1 (rw_cells_app usegs m A _ _)). rewrite firstn_skipn. exact HC. Qed.

  Lemma rw_cells_uncut : forall m A cs1 cs2 A2,
    rw_cells usegs m A cs1 -> rw_cells usegs m A2 cs2 -> A2 = A + Z.of_nat (cells_size cs1) -> rw_cells usegs m A (cs1 ++ cs2).
  Proof using Type. pin_using tt. intros m A cs1 cs2 A2 HC1 HC2 ->. apply (proj2 (rw_cells_app usegs m A _ _)). split; assumption. Qed.

  Definition set_pj_g (g : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) g (pj_h j) (pj_breakloop j).
  Definition set_pj_f (f : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) f (pj_g j) (pj_h j) (pj_breakloop j).
  Definition set_pj_h (h : list byte) (j : pcap_junk) : pcap_junk :=
    mkPJ (pj_read_op j) (pj_fd j) (pj_a j) (pj_b j) (pj_c j) (pj_d j) (pj_e j) (pj_f j) (pj_g j) h (pj_breakloop j).

  Remark pc_pre_size : forall p P B rf j, csize rf = 8%nat -> cells_size (pc_pre p P B rf j) = 216%nat.
  Proof using Type. pin_using tt. intros p P B rf j Hrf. cbn. rewrite Hrf. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma pcap_cells_split4 : forall m P p B rf st os j,
    csize rf = 8%nat ->
    rw_cells usegs m P (pcap_cells_gen p P B rf st os j) ->
    rw_cells usegs m P (pc_pre p P B rf j) /\ rw_cells usegs m (P + 216) [CB 304 (pj_g j)]
    /\ rw_cells usegs m (P + 520) (hdr_cells (pc_header p)) /\ rw_cells usegs m (P + 544) (pc_ops p st os j).
  Proof using Type. pin_using tt.
    intros m P p B rf st os j Hrf HC. unfold pcap_cells_gen in HC.
    apply rw_cells_app in HC as [H1 HC]. rewrite (pc_pre_size p P B rf j Hrf) in HC.
    apply rw_cells_app in HC as [H2 HC]. cbn [cells_size csize Nat.add] in HC.
    apply rw_cells_app in HC as [H3 H4]. cbn [cells_size csize Nat.add hdr_cells] in H4.
    replace (P + Z.of_nat 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) in H4 by lia.
    replace (P + Z.of_nat 216 + Z.of_nat 304) with (P + 520) in H3 by lia.
    replace (P + Z.of_nat 216) with (P + 216) in H2 by lia. auto.
  Qed.

  Lemma pcap_cells_join4 : forall m P p B rf st os j cs h,
    csize rf = 8%nat ->
    rw_cells usegs m P (pc_pre p P B rf j) -> rw_cells usegs m (P + 216) cs -> cells_size cs = 304%nat ->
    rw_cells usegs m (P + 520) (hdr_cells h) -> rw_cells usegs m (P + 544) (pc_ops p st os j) ->
    rw_cells usegs m P (pcap_cells_gen (set_header h p) P B rf st os (set_pj_g (cells_bytes cs) j)).
  Proof using Type. pin_using tt.
    intros m P p B rf st os j cs h Hrf H1 H2 Hcs H3 H4. unfold pcap_cells_gen.
    assert (E1 : pc_pre (set_header h p) P B rf (set_pj_g (cells_bytes cs) j) = pc_pre p P B rf j).
    { unfold pc_pre, np_entry, is_ng. destruct p; reflexivity. }
    assert (E2 : pc_ops (set_header h p) st os (set_pj_g (cells_bytes cs) j) = pc_ops p st os j).
    { unfold pc_ops, cleanup_entry, is_ng. destruct p; reflexivity. }
    rewrite E1, E2. replace (pc_header (set_header h p)) with h by (destruct p; reflexivity). cbn [pj_g set_pj_g].
    apply rw_cells_app. split; [exact H1|]. rewrite (pc_pre_size p P B rf j Hrf).
    pose proof (rw_cells_merge usegs m (P + 216) [] cs (hdr_cells h ++ pc_ops p st os j)) as M. cbn [app] in M. rewrite Hcs in M.
    replace (P + Z.of_nat 216) with (P + 216) by lia. apply M.
    apply rw_cells_app. split; [exact H2|]. rewrite Hcs. apply rw_cells_app. split.
    - replace (P + 216 + Z.of_nat 304) with (P + 520) by lia. exact H3.
    - cbn [cells_size csize hdr_cells Nat.add]. replace (P + 216 + Z.of_nat 304 + Z.of_nat 24) with (P + 544) by lia. exact H4.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_recell : forall m A cs cs',
    rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
  Proof using Type. pin_using tt.
    intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf'| rewrite Heq; exact Hb]|].
    rewrite <- (cells_bytes_length cs' Hwf'), Heq, (cells_bytes_length cs Hwf). exact Hw.
  Qed.

  (* [comment removed for export] *)
  Definition pack2 (lo hi : word) : word := Z_to_bv 64 (bv_unsigned lo mod 2^32 + 2^32 * (bv_unsigned hi mod 2^32)).
  Definition hdr3 (h : pkthdr) : list cell :=
    [C8 (Z_to_bv 64 (h_sec h)); C8 (Z_to_bv 64 (h_usec h)); C8 (pack2 (Z_to_bv 64 (h_caplen h)) (Z_to_bv 64 (h_len h)))].

  Lemma Z_to_le_bytes_split : forall a b z, (0 <= z)%Z ->
    Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
  Proof using Type. pin_using tt.
    induction a as [|a IH]; intros b z Hz.
    - cbn [Nat.add app Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
    - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH by (apply Z.shiftr_nonneg; lia). f_equal. f_equal.
      rewrite Z.shiftr_shiftr by lia. f_equal. lia.
  Qed.

  Lemma le8_pack2 : forall lo hi, le8 (pack2 lo hi) = le4 lo ++ le4 hi.
  Proof using Type. pin_using tt.
    intros lo hi. unfold pack2, le8, le4, word_to_le_bytes.
    pose proof (Z.mod_pos_bound (bv_unsigned lo) (2^32) ltac:(lia)) as H1.
    pose proof (Z.mod_pos_bound (bv_unsigned hi) (2^32) ltac:(lia)) as H2.
    rewrite unsigned_lit by lia. change 8%nat with (4 + 4)%nat at 1. rewrite Z_to_le_bytes_split by lia. f_equal.
    - rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned lo) 32) by (cbn; lia). f_equal.
      rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    - rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned hi) 32) by (cbn; lia). f_equal.
      change (8 * Z.of_nat 4)%Z with 32%Z. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. reflexivity.
  Qed.

  Lemma hdr3_bytes : forall h, cells_bytes (hdr3 h) = cells_bytes (hdr_cells h).
  Proof using Type. pin_using tt. intros h. cbn [cells_bytes cbytes hdr3 hdr_cells]. rewrite le8_pack2, <- app_assoc. reflexivity. Qed.

  Lemma hdr_cells_to_3 : forall m A h, rw_cells usegs m A (hdr_cells h) -> rw_cells usegs m A (hdr3 h).
  Proof using Type. pin_using tt. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | apply hdr3_bytes]. Qed.
  Lemma hdr_cells_of_3 : forall m A h, rw_cells usegs m A (hdr3 h) -> rw_cells usegs m A (hdr_cells h).
  Proof using Type. pin_using tt. intros m A h HC. eapply rw_cells_recell; [exact HC| cbn; repeat split; exact I | symmetry; apply hdr3_bytes]. Qed.

  (* [comment removed for export] *)
  Lemma PCAPRg_blocks : forall P p PB rf st os m, PCAPRg P p PB rf st os m ->
    exists B I, PB = pcap_blocks p P B I.
  Proof using Type. pin_using tt. intros P p PB rf st os m (B & I & j & pad & bs & E & _). exists B, I. exact E. Qed.

  Lemma PCAPR_self_in : forall P p PB FB m, PCAPR P p PB FB m -> In (pc_self p, P, psize p) PB.
  Proof using Type. pin_using tt. intros P p PB FB m (Af & _ & (B & I & j & pad & bs & -> & _)). left. reflexivity. Qed.

  Lemma psize_pos : forall p, 664 <= psize p <= 680.
  Proof using Type. pin_using tt. intros p. unfold psize, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL. destruct (is_ng p); lia. Qed.

  (* [comment removed for export] *)
  Definition pcap_iv (R : rctx) (PB : list cblk) (iv : Z * Z) : Prop :=
    (rc_lo R <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block PB iv.

  Lemma GIo_pcap_frame : forall R s CLc PB FB m m' W,
    GIo R s (CLc ++ PB) FB m -> munch W m m' -> wmono usegs m m' -> Forall (pcap_iv R PB) W ->
    GIo R s (CLc ++ PB) FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CLc PB FB m m' W G MU WM HW. eapply GIo_client_frame; [exact G|exact MU|exact WM|].
    apply Forall_impl with (2 := HW). intros iv [Hs|Hb]; [left; exact Hs| right].
    unfold iv_in_block in *. rewrite Exists_app. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_pcap_writes : forall R s CLc PB FB m m' W SP,
    GIo R s (CLc ++ PB) FB m -> munch W m m' -> wmono usegs m m' ->
    Forall (fun iv => (rc_lo R <= fst iv /\ snd iv <= SP) \/ iv_in_block PB iv) W -> rc_lo R <= SP ->
    agrees_on (client_keeps CLc SP) m m'.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m m' W SP G MU WM HW HSP.
    pose proof (GIo_blocks _ _ _ _ _ G) as [BO BA]. pose proof (GIo_spw _ _ _ _ _ G) as SPW.
    apply blocks_apart_app_inv in BA as (BA1 & _ & _). apply blocks_apart_app_inv in BA1 as (_ & _ & BAX).
    apply Forall_app in BO as [BO _]. apply Forall_app in BO as [BOc BOp].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hlo|Hb]; cbn [fst snd] in *.
    - destruct Hk as [Hk|Hk]; [lia|]. apply in_block_In in Hk as (b & Hbin & Hb).
      pose proof (proj1 (Forall_forall _ _) BOc b Hbin) as (K1 & K2 & K3 & K4 & K5 & K6). unfold rc_lo in HSP, Hlo.
      unfold cb_addr, cb_size in *. lia.
    - unfold iv_in_block in Hb. apply Exists_exists in Hb as (b' & Hb'in & Hlo' & Hhi'). cbn [fst snd] in Hlo', Hhi'.
      pose proof (proj1 (Forall_forall _ _) BOp b' Hb'in) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Hk as [Hk|Hk]; [unfold rc_lo in HSP; lia|]. apply in_block_In in Hk as (b & Hbin & Hb).
      pose proof (BAX b b' Hbin Hb'in) as AP. unfold apart in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_PB_block : forall R s CLc PB FB m q A n, GIo R s (CLc ++ PB) FB m -> In (q, A, n) PB ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x56000 <= A)
    /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m q A n G Hin.
    pose proof (GIo_block_ok _ _ _ _ _ (q, A, n) G ltac:(apply in_or_app; left; apply in_or_app; right; exact Hin)) as (K1 & K2 & K3 & K4 & K5 & K6).
    cbn [cb_addr cb_size fst snd] in *. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_apart : forall R s CL FB m b b', GIo R s CL FB m -> In b (CL ++ FB) -> In b' (CL ++ FB) -> b = b' \/ apart b b'.
  Proof using Type. pin_using tt. intros R s CL FB m b b' G H1 H2. exact (blocks_apart_In _ _ _ (proj2 (GIo_blocks _ _ _ _ _ G)) H1 H2). Qed.

  (* [comment removed for export] *)
  Lemma sp_above_blocks : forall (sp : word) R s CL FB m lo budget (tp : word),
    std_pre_o sp tp R s CL FB lo budget m -> 0 <= budget -> CEILZ <= bv_unsigned sp - budget /\ bv_unsigned sp <= rc_spmain R /\ 0x7fff80000000 <= usp0 R.
  Proof using Type. pin_using tt.
    intros sp R s CL FB m lo budget tp (G & ST & LO & BU & SPM & MI & TP & ALN) Hb.
    pose proof (GIo_spw _ _ _ _ _ G) as [SPWa SPWb]. unfold rc_lo in LO. split; [lia|]. split; [exact SPM| exact SPWa].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma priv_cells_size : forall p I pad, length pad = 4%nat ->
    cells_size (priv_cells p I pad) = (if is_ng p then 32 else 16)%nat.
  Proof using Type. pin_using tt. intros p I pad Hp. unfold priv_cells, is_ng. destruct (pc_priv p); cbn; reflexivity. Qed.

  Lemma priv_cells_size_le : forall m P p I pad, rw_cells usegs m P (priv_cells p I pad) -> (Z.of_nat (cells_size (priv_cells p I pad)) <= 32)%Z.
  Proof using Type. pin_using tt.
    intros m P p I pad [[Hwf _] _]. unfold priv_cells in *. destruct (pc_priv p); cbn in *; [lia|].
    destruct Hwf as (_ & _ & _ & _ & Hl & _). cbn in Hl. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PB_apart : forall R s CLc PB FB m p P B I,
    GIo R s (CLc ++ PB) FB m -> PB = pcap_blocks p P B I ->
    (P + psize p <= B \/ B + pc_bufalloc p <= P)
    /\ (forall sg q, pc_priv p = PrivNg sg (Some q) ->
          (P + psize p <= I \/ I + 40 * ng_ifaces_size sg <= P) /\ (B + pc_bufalloc p <= I \/ I + 40 * ng_ifaces_size sg <= B)).
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m p P B I G EPB.
    pose proof (proj2 (GIo_blocks _ _ _ _ _ G)) as BA.
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & BA & _).
    rewrite EPB in BA. unfold pcap_blocks in BA. cbn [blocks_apart] in BA.
    destruct BA as (F1 & F2 & _). pose proof (Forall_inv F1) as A12. apply Forall_inv_tail in F1.
    unfold apart, cb_addr, cb_size in A12; cbn [fst snd] in A12. split; [lia|].
    intros sg q Hq. rewrite Hq in F1, F2. pose proof (Forall_inv F1) as A13. pose proof (Forall_inv F2) as A23.
    unfold apart, cb_addr, cb_size in A13, A23; cbn [fst snd] in A13, A23. lia.
  Qed.

  Lemma if_cells_size : forall i j, cells_size (if_cells i j) = 40%nat.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  Lemma ifs_cells_size : forall ifs js, length js = length ifs -> cells_size (ifs_cells ifs js) = (40 * length ifs)%nat.
  Proof using Type. pin_using tt.
    induction ifs as [|i ifs IH]; intros [|j0 js0] Hlen; cbn [length] in Hlen; try discriminate Hlen.
    - reflexivity.
    - cbn [ifs_cells]. rewrite cells_size_app, if_cells_size, (IH js0) by lia. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ifaces_ok_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_ok p I m -> ifaces_ok p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p I m m' Q AG HQ IFS. unfold ifaces_ok in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as (js & tail & Hl & HC & H1 & H2 & H3 & H4). exists js, tail. split; [exact Hl|]. split; [|repeat split; try assumption; lia].
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl).
    pose proof (rw_cells_bound _ _ _ _ HC) as HB.
    rewrite cells_size_app in Ha, HB. cbn [cells_size csize] in Ha, HB. rewrite Nat.add_0_r in Ha, HB.
    rewrite ifs_cells_size in Ha by (rewrite length_rev; lia). rewrite length_rev in Ha. lia.
  Qed.

  Lemma priv_cells_psize : forall m A p I pad, rw_cells usegs m A (priv_cells p I pad) ->
    Z.of_nat (cells_size (priv_cells p I pad)) = psize p - PCAP_PRIV_OFF.
  Proof using Type. pin_using tt.
    intros m A p I pad [[Hwf _] _]. unfold priv_cells, psize, is_ng, PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL, PCAP_SF_TOTAL in *.
    destruct (pc_priv p); cbn in *; lia.
  Qed.

  Lemma pcap_aux_agree : forall p P B I pad bs m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall a, B <= a < B + pc_bufalloc p -> Q a) ->
    (forall a, P + PCAP_PRIV_OFF <= a < P + psize p -> Q a) ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    0 <= pc_bufalloc p ->
    rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] -> rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> ifaces_ok p I m ->
    rw_cells usegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs] /\ rw_cells usegs m' (P + PCAP_PRIV_OFF) (priv_cells p I pad) /\ ifaces_ok p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p P B I pad bs m m' Q AG HB HP HI Hba BUF PRIV IFS. split; [|split].
    - eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply HB. cbn [cells_size csize] in Ha. lia.
    - eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply HP. pose proof (priv_cells_psize _ _ _ _ _ PRIV). lia.
    - eapply ifaces_ok_agree; eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma pcap_cells_gen_size : forall p P B rf st os j, csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    cells_size (pcap_cells_gen p P B rf st os j) = 648%nat.
  Proof using Type. pin_using tt. intros p P B rf st os j H1 H2 H3. unfold pcap_cells_gen. rewrite !cells_size_app. cbn. rewrite H1, H2, H3. reflexivity. Qed.


  (* [comment removed for export] *)
  Lemma PCAPRg_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg P p PB rf st os m -> PCAPRg P p PB rf st os m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_ok_agree; [exact AG| exact Q3| exact IFS].
  Qed.

  Lemma PCAPR_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR P p PB FB m -> PCAPR P p PB FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ifaces_ok_closable : forall p I m, ifaces_ok p I m -> ifaces_closable p I m.
  Proof using Type. pin_using tt.
    intros p I m HI. unfold ifaces_ok, ifaces_closable in *. destruct (pc_priv p) as [sf|s [q|]]; [exact HI| |tauto].
    destruct HI as (js & tail & Ljs & CE & E1 & E2 & E3 & E4). split; [|exact E3].
    rewrite <- (app_nil_r [CB (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s))) tail]), app_assoc in CE.
    apply (rw_cells_merge usegs m I [] _ []) in CE. cbn [app] in CE. rewrite cells_size_app, ifs_cells_size in CE by (rewrite length_rev; lia).
    cbn [cells_size csize Nat.add] in CE. rewrite length_rev in CE.
    replace (40 * length (ng_ifaces s) + (Z.to_nat (40 * (ng_ifaces_size s - ng_ifcount s)) + 0))%nat with (Z.to_nat (40 * ng_ifaces_size s)) in CE by lia.
    eexists. exact CE.
  Qed.
  Lemma PCAPR_closable_of : forall P p PB FB m, PCAPR P p PB FB m -> PCAPR_closable P p PB FB m.
  Proof using Type. pin_using tt.
    intros P p PB FB m (Af & Hin & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    exists Af. split; [exact Hin|]. exists B, I, j, pad, bs. repeat (split; [assumption|]). split; [apply ifaces_ok_closable; exact IFS| exact WF].
  Qed.

  Lemma ifaces_closable_agree : forall p I m m' (Q : Z -> Prop),
    agrees_on Q m m' ->
    (forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a) ->
    ifaces_closable p I m -> ifaces_closable p I m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros p I m m' Q AG HQ IFS. unfold ifaces_closable in *. destruct (pc_priv p) as [sf|sg [q|]] eqn:E; try exact IFS.
    destruct IFS as ((junk & HC) & H3). split; [|exact H3]. exists junk.
    eapply agrees_rw_cells; [exact AG| exact HC|]. intros a Ha. apply (HQ sg q eq_refl). cbn [cells_size csize] in Ha. lia.
  Qed.
  Lemma PCAPRg_closable_agree : forall P p PB rf st os m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> csize rf = 8%nat -> csize st = 8%nat -> csize os = 8%nat ->
    PCAPRg_closable P p PB rf st os m -> PCAPRg_closable P p PB rf st os m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB rf st os m m' Q AG HQ Hrf Hst Hos (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF).
    exists B, I, j, pad, bs. split; [exact EPB|].
    pose proof (psize_pos p) as PS. pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ. unfold PCAP_PRIV_OFF in PZ.
    pose proof WF as (_ & _ & W3 & _).
    assert (Q1 : forall a, P <= a < P + psize p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q2 : forall a, B <= a < B + pc_bufalloc p -> Q a).
    { intros a Ha. apply HQ. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    assert (Q3 : forall sg q, pc_priv p = PrivNg sg (Some q) -> forall a, I <= a < I + 40 * ng_ifaces_size sg -> Q a).
    { intros sg q Hq a Ha. apply HQ. rewrite EPB. unfold pcap_blocks. rewrite Hq. unfold in_block.
      do 2 apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    split. { eapply agrees_rw_cells; [exact AG|exact CELLS|]. intros a Ha. rewrite (pcap_cells_gen_size p P B rf st os j Hrf Hst Hos) in Ha. apply Q1. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact PRIV|]. intros a Ha. apply Q1. unfold PCAP_PRIV_OFF in Ha. lia. }
    split. { eapply agrees_rw_cells; [exact AG|exact BUF|]. intros a Ha. apply Q2. cbn [cells_size csize] in Ha. lia. }
    split; [exact PFX|]. split; [|exact WF]. eapply ifaces_closable_agree; [exact AG| exact Q3| exact IFS].
  Qed.
  Lemma PCAPR_closable_agree : forall P p PB FB m m' (Q : Z -> Prop),
    agrees_on Q m m' -> (forall a, in_block PB a -> Q a) -> PCAPR_closable P p PB FB m -> PCAPR_closable P p PB FB m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros P p PB FB m m' Q AG HQ (Af & Hin & PG). exists Af. split; [exact Hin|].
    eapply PCAPRg_closable_agree; [exact AG|exact HQ|reflexivity|reflexivity|reflexivity|exact PG].
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_new_file_not_out : heap_addr_law K HO -> forall R s s2 CL CL2 FB f Af m m2,
    GIo R s CL FB m -> GIo R s2 CL2 ((f, Af, FILE_BLOCK) :: FB) m2 -> ps_outfile s2 = ps_outfile s -> ps_outfile s2 <> Some f.
  Proof using Type. pin_using tt.
    intros HAL R s s2 CL CL2 FB f Af m m2 G G2 E C.
    pose proof (proj1 (proj2 (proj2 G))) as HR. rewrite <- E, C in HR. destruct HR as (_ & _ & (A & HinA & _)).
    pose proof (GIo_addr HAL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; left; reflexivity)) as E1.
    pose proof (GIo_addr HAL _ _ _ _ _ _ _ _ G2 ltac:(apply in_or_app; right; right; exact HinA)) as E2.
    pose proof (GIo_blocks _ _ _ _ _ G2) as [_ BA]. apply blocks_apart_app_inv in BA as (_ & BA & _).
    destruct BA as [HF _]. apply (proj1 (Forall_forall _ _) HF) in HinA. unfold apart, FILE_BLOCK in HinA. cbn [cb_addr cb_size fst snd] in HinA. lia.
  Qed.

  Lemma in_PB_below : forall R s CLc PB FB m a, GIo R s (CLc ++ PB) FB m -> in_block PB a -> 0 < a < CEILZ.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m a G Hin. apply in_block_In in Hin as ([[q A] n] & HbIn & Hb). cbn [cb_addr cb_size fst snd] in Hb.
    pose proof (GIo_PB_block _ _ _ _ _ _ _ _ _ G HbIn) as (K1 & K2 & K3 & K4 & K5 & K6). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma GIo_CLc_facts : forall R s CLc PB FB m a, GIo R s (CLc ++ PB) FB m -> in_block CLc a -> 0 < a < CEILZ /\ ~ in_block PB a.
  Proof using Type. pin_using tt.
    intros R s CLc PB FB m a G Hin. pose proof (GIo_blocks _ _ _ _ _ G) as [BO BA].
    apply Forall_app in BO as [BO _]. apply Forall_app in BO as [BOc BOp].
    apply blocks_apart_app_inv in BA as (BA & _ & _). apply blocks_apart_app_inv in BA as (_ & _ & BAX).
    split; [destruct (in_block_facts _ _ _ BOc Hin) as (F1 & F2 & _); lia|].
    intros Hin'. apply in_block_In in Hin as (b & Hb & Hr). apply in_block_In in Hin' as (b' & Hb' & Hr').
    pose proof (BAX b b' Hb Hb') as AP. unfold apart in AP. lia.
  Qed.

  Lemma pcap_wf_set_header : forall p h, pcap_wf p -> 0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 -> pcap_wf (set_header h p).
  Proof using Type. pin_using tt. intros p h WF Hc Hl. unfold pcap_wf in *. destruct p; cbn in *. repeat split; try lia; tauto. Qed.

  (* [comment removed for export] *)
  Lemma PCAPR_intro_set_header : forall P p PB FB m h Af B I j pad bs,
    In (pc_rfile p, Af, FILE_BLOCK) FB -> PB = pcap_blocks p P B I ->
    rw_cells usegs m P (pcap_cells_gen (set_header h p) P B (C8 (Z_to_bv 64 Af)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) j) ->
    rw_cells usegs m (P + PCAP_PRIV_OFF) (priv_cells p I pad) -> rw_cells usegs m B [CB (Z.to_nat (pc_bufalloc p)) bs] ->
    firstn (length (pc_bufdata p)) bs = map b8 (pc_bufdata p) -> ifaces_ok p I m -> pcap_wf p ->
    0 <= h_caplen h < 2^32 -> 0 <= h_len h < 2^32 ->
    PCAPR P (set_header h p) PB FB m.
  Proof using Type. pin_using tt.
    intros P p PB FB m h Af B I j pad bs Hin EPB HC HP HB PFX IFS WF Hc Hl.
    pose proof (pcap_wf_set_header p h WF Hc Hl) as WF'.
    exists Af. split; [destruct p; exact Hin|]. exists B, I, j, pad, bs.
    split; [destruct p; exact EPB|]. split; [exact HC|]. split; [destruct p; exact HP|]. split; [destruct p; exact HB|].
    split; [destruct p; exact PFX|]. split; [destruct p; exact IFS| exact WF'].
  Qed.
End Rep.
End WithCeil.

Arguments pcap_junk : clear implicits.
Arguments if_junk : clear implicits.
End TwB.
