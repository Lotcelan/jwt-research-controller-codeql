/**
 * @name JWK Parameter Misuse in JWT Decode
 * @description Using an unverified JWK from the token header as the key for verification
 * @problem.severity error
 * @security-severity 9.0
 * @precision high
 * @kind path-problem
 * @id py/jwt-jwk-misuse
 * @tags security
 */

import python
import semmle.python.dataflow.new.DataFlow
import semmle.python.dataflow.new.TaintTracking
import semmle.python.Concepts
import semmle.python.ApiGraphs
import semmle.python.dataflow.new.RemoteFlowSources
import Frameworks
import JWT
import Concepts


// First phase: track from get_unverified_header to jwk subscription
private module HeaderToJwkConfig implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
        exists(API::CallNode call, API::Node get_unverified_header_method |
            get_unverified_header_method = API::moduleImport("jwt").getMember("get_unverified_header") and
            call = get_unverified_header_method.getACall() and
            source = call
        )
    }
    
    predicate isSink(DataFlow::Node sink) {
        exists(Subscript sub |
            sub.getObject() = sink.asExpr() and
            sub.getIndex().(StringLiteral).getText() = "jwk"
        )
    }
    
    predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
        DataFlow::localFlowStep(pred, succ)
    }
}

module HeaderToJwk = TaintTracking::Global<HeaderToJwkConfig>;

// Second phase: track from jwk to decode sink
private module JwkToDecodeConfig implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
        exists(HeaderToJwk::PathNode headerSource, HeaderToJwk::PathNode headerSink, Subscript sub |
            HeaderToJwk::flowPath(headerSource, headerSink) and
            headerSink.getNode().asExpr() = sub.getObject() and
            sub.getIndex().(StringLiteral).getText() = "jwk" and
            source.asExpr() = sub
        )
    }
    
    predicate isSink(DataFlow::Node sink) {
        exists(API::CallNode call, API::Node decode_method |
            decode_method = API::moduleImport("jwt").getMember("decode") and
            call = decode_method.getACall() and
            call.getArgByName("key") = sink
        )
    }
    
    predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
        // Your existing flow steps
        DataFlow::localFlowStep(pred, succ)
        or
        exists(DataFlow::CallCfgNode call |
            pred = call.getArg(_) and
            succ = call
        )

        or 
        exists(DataFlow::CallCfgNode call, string name |
            pred = call.getArgByName(name) and
            succ = call
        )

        or

    
        exists(DataFlow::CallCfgNode call, Attribute attr |
            attr = call.getFunction().asExpr() and  // The attribute being called
            pred.asExpr() = attr.getObject() and    // pred is the object (a in a.b())
            succ = call                            // succ is the call result
        )
    }
}

module JwkToDecode = TaintTracking::Global<JwkToDecodeConfig>;

// Use the second flow for reporting
from JwkToDecode::PathNode source, JwkToDecode::PathNode sink
where JwkToDecode::flowPath(source, sink)
select sink.getNode(), source, sink, "JWT decode using unverified JWK from token header"