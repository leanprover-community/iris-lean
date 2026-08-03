-- Axiomatic-semantics framework (pure `HeapLangAxioms` fragment)
import IrisDoNightly.AxSem
import IrisDoNightly.Notation

-- Heap-free codec examples (approach 2), one file per codec
import IrisDoNightly.Codec.Delta
import IrisDoNightly.Codec.Mtf
import IrisDoNightly.Codec.Rle
import IrisDoNightly.Codec.Lzss

-- Proof-automation infrastructure (vcgen-steppable @[spec] set) and framework-gap MWEs
import IrisDoNightly.Codec.Auto
import IrisDoNightly.Codec.DeltaRoundtrip
import IrisDoNightly.Codec.RleRoundtrip
import IrisDoNightly.Codec.PipelineRoundtrip
import IrisDoNightly.MWE.SubstNormalization
import IrisDoNightly.MWE.CompositionHang

-- Legacy: the separation-logic experiments, superseded by the heap-free `Codec/` approach
import IrisDoNightly.Legacy.Array
import IrisDoNightly.Legacy.Loop
import IrisDoNightly.Legacy.SLFrame
import IrisDoNightly.Legacy.Delta
import IrisDoNightly.Legacy.CodecPrelude
import IrisDoNightly.Legacy.Codecs
import IrisDoNightly.Legacy.Pipeline
